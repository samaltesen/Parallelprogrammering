
//Prototype implementation of Car Control
//Mandatory assignment
//Course 02158 Concurrent Programming, DTU, Fall 2017

//Hans Henrik Lovengreen     Oct 9, 2017


import java.awt.Color;

class Gate {

    Semaphore g = new Semaphore(0);
    Semaphore e = new Semaphore(1);
    boolean isopen = false;

    public void pass() throws InterruptedException {
        g.P(); 
        g.V();
    }

    public void open() {
        try { e.P(); } catch (InterruptedException e) {}
        if (!isopen) { g.V();  isopen = true; }
        e.V();
    }

    public void close() {
        try { e.P(); } catch (InterruptedException e) {}
        if (isopen) { 
            try { g.P(); } catch (InterruptedException e) {}
            isopen = false;
        }
        e.V();
    }

}

class Car extends Thread {
    Field playGround = Field.getInstance();
    int basespeed = 100;             // Rather: degree of slowness
    int variation =  0;             // Percentage of base speed

    CarDisplayI cd;                  // GUI part

    int no;                          // Car number
    Pos startpos;                    // Startpositon (provided by GUI)
    Pos barpos;                      // Barrierpositon (provided by GUI)
    Color col;                       // Car  color
    Gate mygate;                     // Gate at startposition


    int speed;                       // Current car speed
    Pos curpos;                      // Current position 
    Pos newpos;                      // New position to go to

    public Car(int no, CarDisplayI cd, Gate g) {

        this.no = no;
        this.cd = cd;
        mygate = g;
        startpos = cd.getStartPos(no);
        barpos = cd.getBarrierPos(no);  // For later use

        col = chooseColor();

        // do not change the special settings for car no. 0
        if (no==0) {
            basespeed = 0;  
            variation = 0; 
            setPriority(Thread.MAX_PRIORITY); 
        }
    }

    public synchronized void setSpeed(int speed) { 
        if (no != 0 && speed >= 0) {
            basespeed = speed;
        }
        else
            cd.println("Illegal speed settings");
    }

    public synchronized void setVariation(int var) { 
        if (no != 0 && 0 <= var && var <= 100) {
            variation = var;
        }
        else
            cd.println("Illegal variation settings");
    }

    synchronized int chooseSpeed() { 
        double factor = (1.0D+(Math.random()-0.5D)*2*variation/100);
        return (int) Math.round(factor*basespeed);
    }

    private int speed() {
        // Slow down if requested
        final int slowfactor = 3;  
        return speed * (cd.isSlow(curpos)? slowfactor : 1);
    }

    Color chooseColor() { 
        return Color.blue; // You can get any color, as longs as it's blue 
    }

    Pos nextPos(Pos pos) {
        // Get my track from display
        return cd.nextPos(no,pos);
    }

    boolean atGate(Pos pos) {
        return pos.equals(startpos);
    }

   public void run() {
        try {

            speed = chooseSpeed();
            curpos = startpos;
            cd.mark(curpos,col,no);
            while (true) { 
                sleep(speed());
  
                if (atGate(curpos)) { 
                    mygate.pass(); 
                    speed = chooseSpeed();
                }
                newpos = nextPos(curpos);
                playGround.checkNewPos(newpos.row,newpos.col,curpos.col,no);
                //  Move to new position 
                cd.clear(curpos);
                cd.mark(curpos,newpos,col,no);
                sleep(speed());
                cd.clear(curpos,newpos);
                cd.mark(newpos,col,no);
                playGround.releaseOldPos(curpos.row, curpos.col);
                curpos = newpos;
                
            }

        } catch (Exception e) {
            cd.println("Exception in Car no. " + no);
            System.err.println("Exception in Car no. " + no + ":" + e);
            e.printStackTrace();
        }
    }

}

public class CarControl implements CarControlI{
    Bridge bridge = Bridge.getInstance();
    Barrier barriere = Barrier.getInstance();
    CarDisplayI cd;           // Reference to GUI
    Car[]  car;               // Cars
    Gate[] gate;              // Gates

    public CarControl(CarDisplayI cd) {
        this.cd = cd;
        car  = new  Car[9];
        gate = new Gate[9];

        for (int no = 0; no < 9; no++) {
            gate[no] = new Gate();
            car[no] = new Car(no,cd,gate[no]);
            car[no].start();
        } 
    }

   public void startCar(int no) {
        gate[no].open();
        setSpeed(no, 20);
    }

    public void stopCar(int no) {
        gate[no].close();
    }

    public void barrierOn() { 
    	barriere.on();
       // cd.println("Barrier On not implemented in this version");
    }

    public void barrierOff() {
    	barriere.off();
        //cd.println("Barrier Off not implemented in this version");
    }

    public void barrierShutDown() { 
        cd.println("Barrier shut down not implemented in this version");
        // This sleep is for illustrating how blocking affects the GUI
        // Remove when shutdown is implemented.
        try { Thread.sleep(3000); } catch (InterruptedException e) { }
        // Recommendation: 
        //   If not implemented call barrier.off() instead to make graphics consistent
    }

    public void setLimit(int k) { 
        bridge.setLimit(k);
        
    }

    public void removeCar(int no) { 
        cd.println("Remove Car not implemented in this version");

        //nY COMMENTAR//nyere kommentar!

    }

    public void restoreCar(int no) { 
        cd.println("Restore Car not implemented in this version");
    }

    /* Speed settings for testing purposes */

    public void setSpeed(int no, int speed) { 
        car[no].setSpeed(speed);
    }

    public void setVariation(int no, int var) { 
        car[no].setVariation(var);
    }

}

class Alley{
       private static Alley instance = null;
       private int nrUp = 0;
       private int nrDown = 0;
       private synchronized void startDown(){
           while(nrUp > 0){
           try{
               wait();
           }
           catch(InterruptedException e){}
           }
           nrDown++; 
       }
       private synchronized void endDown(){
       nrDown--;
       if (nrDown == 0){
           notify();
       }
       }
       private synchronized void startUp(){
           while(nrDown > 0){
           try{
               wait();
           }
           catch(InterruptedException e){}
           }
           nrUp++; 
       }
       private synchronized void endUp(){
       nrUp--;
       if (nrUp == 0){
           notify();
       }
       }
	public  void enter(int no) {

             if(no < 5){
                 startDown();
            }
                
            else{
                 startUp();
            }
        }   	
	public void leave(int no) {
                if (no < 5){
                    endDown();
                }
                else{
                    endUp();
                }            
                
         } 
        
        public int getNrDown(){
            return nrDown;
        }
        
        public static Alley getInstance() {
            if (instance == null) {
                instance =  new Alley();
            }
        return instance;
        }
}

class Barrier {
	   private static Barrier instance = null;
	   private  boolean barriere = false;
	   private int carsWaiting = 0;
	   protected Barrier(){}
	   public synchronized void sync(){
		if(barriere) {
                    carsWaiting++;
                    if(carsWaiting == 9){
                        carsWaiting = 0;
                        notifyAll();
                    }
                    else{
                            try{
                                wait();
                            }
                            catch(InterruptedException e){}
                       }
                }
	   }

           public boolean getBarriere(){
               return barriere;
           }
           
	   public synchronized void on() {       
               
		   barriere = true;
            
           }

    public synchronized void off() {
        barriere = false;
        if(carsWaiting > 0){
            carsWaiting = 0;
            notifyAll();
        }
    }   
    
    public static Barrier getInstance() {
         if (instance == null) {
	instance =  new Barrier();
        }
        return instance;
    }
}
class Bridge{
   private Alley alley = Alley.getInstance();
   private int limit = 6;
   private int counter = 0;
   private static Bridge instance = null;

   public synchronized void enter(int no){
       while(counter == limit){
           try{
               wait();
           }
           catch(InterruptedException e){
           
           }
       }
       while(limit < 5 && alley.getNrDown() > 0 && counter == limit-1 && no > 4){
           notify();
           try{
               wait();
           }
           catch(InterruptedException e){
           
           }
       }

       counter++;

   }

   public synchronized void leave(int no){
    counter--;
    notify();
   }

   public void setLimit(int k){
    limit = k;
   
   }
   
   public static Bridge getInstance(){
       if (instance == null){
           instance = new Bridge();
       }
       return instance;
   }
}

class Field{
    private  Barrier barrier = Barrier.getInstance();
    private Alley alley = Alley.getInstance();
    private Bridge bridge = Bridge.getInstance();
	private static Field instance = null;
	Semaphore[][] fields;
	protected Field(int row,int col) {
		fields = new Semaphore[row][col];
		for(int i = 0 ; i < row ; i++) {
			for(int j = 0 ; j < col ; j++) {
				fields[i][j] = new Semaphore(1);
			}			
		}
		
	}
	//singleton design pattern, share the field object across the multiple instances of cars.
	public static Field getInstance() {
		if (instance == null) {
			instance = new Field(11,12);
		}
		return instance;
	}
	
	public void checkNewPos(int rowNew,int colNew, int colOld,int no) {
            //Check if we are about to enter alley
            if(( colNew == 0 && rowNew == 2 && colOld != 0) || ( colNew == 0 && rowNew == 11 && colOld != 0) || ( colNew == 0 && rowNew == 10) || (no == 3 && colNew == 3 && colOld == 4 && rowNew == 1) || (no == 4 && colNew == 3 && colOld == 4 && rowNew == 1) ){
                alley.enter(no);
                
            }
            //check if the cars has left the alley//moved col when we implemented bridge to avoid deadlock 
            if(((colNew == 2) && (colOld == 1) && (no < 5)||(no > 4)&& colNew == 2 && rowNew == 0)){
                alley.leave(no);
                
            }
            //are we at the barriere
            if((no<5 && rowNew == 5 && colNew > 2 && barrier.getBarriere()) || (no > 4 && rowNew == 6 && colNew > 2 && barrier.getBarriere())){
            	barrier.sync();
            	
            }
            //are we about to enter the bridge?
            if((rowNew == 9 && colOld == 0 && colNew == 1 && no < 5) ||(colNew == 3 && rowNew == 10)){
                bridge.enter(no);
            }
            //have we left the bridge?
            if(((rowNew == 8 || rowNew==9) && colOld == 4 && no < 5) ||(colOld== 0 && rowNew == 9 && no > 4)){
                bridge.leave(no);
            }
            //if none of the above, then check if the next field on the playground is free
		try {
			fields[rowNew][colNew].P();
		} catch (InterruptedException e) {
			e.printStackTrace();
		  }
	}
            //Release the old field on the playground
            public void releaseOldPos(int row,int col) {
		fields[row][col].V();
            }
	
}






