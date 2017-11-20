
//Prototype implementation of Car Control
//Mandatory assignment
//Course 02158 Concurrent Programming, DTU, Fall 2017

//Hans Henrik Lovengreen     Oct 9, 2017


import java.awt.Color;
import java.util.LinkedList;
import java.util.Queue;

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
        //return speed * (cd.isSlow(curpos)? slowfactor : 1);
        return speed*slowfactor;
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
        cd.println("Setting of bridge limit not implemented in this version");
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
	private Semaphore enter = new Semaphore(1);
    private Semaphore up = new Semaphore(1);
    private Semaphore down = new Semaphore(1);
    
    private int carsUp = 0;
    private int carsDown = 0;
    
    public void enter(int no) throws InterruptedException {
	    if(no < 5 && no != 0) {
	    	down.P();
	    	if(carsDown == 0) {
	    		enter.P();
	    	}
	    	carsDown++;
	    	down.V();
	    } else {
	    	up.P();
	    	if(carsUp == 0) {
	    		enter.P();
	    	}
	    	carsUp++;
	    	up.V();
	    	
	    }
	    
    }
    
    public void leave(int no) throws InterruptedException {
    	if(no < 5 && no != 0) {
    		down.P();
    		carsDown--;
    		if(carsDown == 0) {
    			enter.V();
    		}
    		down.V();
    	} else {
    		up.P();
    		carsUp--;
    		if(carsUp == 0) {
    			enter.V();
    		}
    		up.V();
    		
    	}
    }
    /*
	//Passing the blaton
       private Semaphore enter = new Semaphore(1);
       private Semaphore up = new Semaphore(0);
       private Semaphore down = new Semaphore(0);
       private int delayedDown = 0;
       private int delayedUp = 0;
       private int nrUp = 0;
       private int nrDown = 0;
	public void enter(int no) {
	
            try {
                if ((no==1) || (no==2) || (no == 3) || (no == 4) ){
                    enter.P();
                    if(nrUp > 0){
                        delayedDown++;
                        enter.V();
                        down.P();
                    }
                    nrDown++;
                    if(delayedDown > 0){
                        delayedDown--;
                        down.V();
                     }
                    else{
                        enter.V();
                    }
                }
                else{
                    enter.P();
                    if(nrDown > 0){
                        delayedUp++;
                        enter.V();
                        up.P();
                    }
                    nrUp++;
                    if(delayedUp > 0){
                        delayedUp--;
                        up.V();
                     }
                    else{
                        enter.V();
                    }
                    
                }
             }
             catch(InterruptedException e){}
                
        }
            	
	public void leave(int no) {
            try{
                if ((no==1) || (no==2) || (no == 3) || (no == 4)){
                    enter.P();
                    nrDown--;
                    if(nrDown == 0 && delayedUp > 0){
                        delayedUp--;
                        up.V();
                    }
                    else{
                        enter.V();
                    }              
                }
                else{
                    enter.P();
                    nrUp--;
                    if(nrUp == 0 && delayedDown > 0){
                        delayedDown--;
                        down.V();
                    }
                    else{
                        enter.V();
                    }              
                
                }   
            }
            catch(InterruptedException e){      
            }
        
	}
	*/
}

class Barrier {
	   private static Barrier instance = null;
	   private  boolean barriere = false;
           private boolean firstTime = true;
	   private int carsWaiting = 0;
	   private Semaphore sp1 = new Semaphore(0);
           private Semaphore sp2 = new Semaphore(1);
           private Semaphore mutex = new Semaphore(1);
	   protected Barrier(){}
           //Reusable barriers the little book of semaphores
	   public void sync(int no) { 
		   if(barriere) {
                   try{    
                       mutex.P();
			   carsWaiting++; 
		   	 if(carsWaiting == 9){
				sp2.P();
                                sp1.V();
                        }
                        mutex.V();
                        sp1.P();
                        sp1.V();
                        
                    mutex.P();
                        carsWaiting--;
                        if(carsWaiting == 0){
                            sp1.P();
                            sp2.V();
                        }
                    mutex.V();
                    sp2.P();
                    sp2.V();
                  }
                   catch(InterruptedException e){}
                   }      
	   }  // Wait for others to arrive (if barrier active)

           public boolean getBarriere(){
               return barriere;
           }
           
	   public void on() { 
            try{ 
               mutex.P();
		   barriere = true;
                   firstTime = true;
		mutex.V();
            }
            catch(InterruptedException e){}
	   }    // Activate barrier

    public void off() {
        try{    
             mutex.P();
                //Why this?
                 carsWaiting++;
                 barriere = false;
		 if(carsWaiting > 0 && firstTime){
                    sp2.P();
                    sp1.V();
                    firstTime = false;
                 }
            mutex.V();
            sp1.P();
            sp1.V();
                        
            mutex.P();
            carsWaiting--;
            if(carsWaiting == 0){
                sp1.P();
                sp2.V();
            }
            mutex.V();
            sp2.P();
            sp2.V();     
        }
        catch(InterruptedException e){}
    }   
    
    
	   public static Barrier getInstance() {
		   if (instance == null) {
			   instance =  new Barrier();
		   }
		   return instance;
	   }
	}

class Field{
	private  Barrier barrier = Barrier.getInstance();
    private Alley alley = new Alley();
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
	
	public void checkNewPos(int rowNew,int colNew, int colOld,int no) throws InterruptedException {
            //Check if we are about to enter alley
            if(/*(colNew == 0 && rowNew == 1 && colOld != 0) ||*/ ( colNew == 0 && rowNew == 2 && colOld != 0) || ( colNew == 0 && rowNew == 11 && colOld != 0) || ( colNew == 0 && rowNew == 10) || (no == 3 && colNew == 3 && colOld == 4 && rowNew == 1) || (no == 4 && colNew == 3 && colOld == 4 && rowNew == 1) ){
                alley.enter(no);
                
            }
            //check if the cars has left the alley
            if(((colNew == 1) && (colOld == 0) && (no==1||no==2||no==3||no==4))||((no == 5||no==6||no==7||no==8)&& colNew == 2 && rowNew == 0)){
                alley.leave(no);
                
            }
            if((no<5 && rowNew == 5 && colNew > 2 && barrier.getBarriere()) || (no > 4 && rowNew == 6 && colNew > 2 && barrier.getBarriere())){
            	barrier.sync(no);
            	
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






