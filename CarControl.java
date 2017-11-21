
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
    Workshop workshop = Workshop.getInstance();
    Alley alley = Alley.getInstance();
    int posCheck = 0;
    int basespeed = 100;             // Rather: degree of slowness
    int variation =  0;             // Percentage of base speed
    boolean clear = false;
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
        final int slowfactor = 4;
        return speed*slowfactor;  
        //return speed * (cd.isSlow(curpos)? slowfactor : 1);
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
        

            speed = chooseSpeed();
            curpos = startpos;
            cd.mark(curpos,col,no);
            while (true) { 
                try {
                    sleep(speed());

                    if (atGate(curpos)) { 
                        mygate.pass(); 
                        speed = chooseSpeed();
                    }

                    newpos = nextPos(curpos);
                    posCheck = playGround.checkNewPos(no,cd,curpos,newpos);
                    if(posCheck == 1) {
                    	alley.enter(no);
                    }
                    else if (posCheck == 2) {
                    	alley.leave(no);
                    }
                    
                    //  Move to new position 
                    cd.clear(curpos);
                    try{
                        cd.mark(curpos,newpos,col,no);
                        sleep(speed());
                    }
                    catch(InterruptedException e){
                        if(workshop.getRemovalFlag(no) && !workshop.getRestoreFlag(no)){
                            cd.clear(curpos, newpos);
                            clear = true;
                        }
                        throw e;
                     }

                    cd.clear(curpos,newpos);
                    try{
                    cd.mark(newpos,col,no);
                    playGround.releaseOldPos(curpos.row, curpos.col);
                    }
                    catch(Exception e){
                        if(workshop.getRemovalFlag(no) && !workshop.getRestoreFlag(no)){
                            cd.clear(newpos);
                            clear = true;
                        }
                        throw e;
                        
                    }
                    curpos = newpos;
                }
                catch (Exception e) {
                    if(!clear && !workshop.getRestoreFlag(no)){
                        cd.clear(curpos);
                    }
                    else{
                        clear = false;
                    }
                    playGround.setPlayfield(no);
                    if(workshop.getRemovalFlag(no) && !workshop.getRestoreFlag(no)){
                        workshop.removeCar(no, curpos);
                        curpos = startpos;
                        cd.mark(curpos,col,no);
                    }
 
                }
                
            }

        
    }

}

public class CarControl implements CarControlI{
    Workshop workshop = Workshop.getInstance();
    CarDisplayI cd;           // Reference to GUI
    Car[]  car;               // Cars
    Gate[] gate;              // Gates
    Pos test;

    
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

       // cd.println("Barrier On not implemented in this version");
    }

    public void barrierOff() {

        //cd.println("Barrier Off not implemented in this version");
    }

    public void barrierShutDown() { 

        // This sleep is for illustrating how blocking affects the GUI
        // Remove when shutdown is implemented.
        //try { Thread.sleep(3000); } catch (InterruptedException e) { }
        // Recommendation: 
        //   If not implemented call barrier.off() instead to make graphics consistent
    }

    public void setLimit(int k) { 
 
        
    }

    public void removeCar(int no) { 
       
        workshop.MarkCarForRemoval(no);
        car[no].interrupt();
        //nY COMMENTAR//nyere kommentar!

    }

    public void restoreCar(int no) {
    	test = new Pos(5,5);
        workshop.MarkCarForRestoration(no);
        //workshop.removeCar(no, test);
        car[no].interrupt();
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
       private synchronized void startDown() throws InterruptedException{
           while(nrUp > 0){
	           try{
	               wait();
	           }
	           catch(InterruptedException e){throw e;}
           }
           
           notify();
           nrDown++; 
       }
       public synchronized void endDown(){
	       nrDown--;
	       if (nrDown == 0){
	           notify();
	       }
       }
       private synchronized void startUp() throws InterruptedException{
           while(nrDown > 0){
	           try{
	               wait();
	           }
	           catch(InterruptedException e){ throw e;}
           }
           notify();
           nrUp++; 
       }
       public synchronized void endUp(){
	       nrUp--;
	       if (nrUp == 0){
	           notify();
	       }
       }
		public synchronized void enter(int no) throws InterruptedException {
		
	         if(no < 5){
	             startDown();
	         }
	            
	         else{
	             startUp();
	         }
	    }   	
		public synchronized void leave(int no) throws InterruptedException{
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

class Workshop{
    private static Workshop instance = null;
    private Alley alley = Alley.getInstance();
    private boolean[] removalFlags =  new boolean[10];
    private boolean[] restoreFlags =  new boolean[10];
    protected Workshop(){
        for (int i = 0 ; i < 10 ; i++){
            removalFlags[i] = false;    
            restoreFlags[i] = false;
        }
    }
    public synchronized void removeCar(int no, Pos current){
        notifyAll();
        
        if(	current.col == 0 ||
        	((no < 5 || no > 2) && current.col < 4 && current.row == 1) || (no < 3 && current.col == 1 && current.row == 2) ||
        	(no >= 5 && ((current.row == 1 && current.col < 3) || (current.row == 10 && current.col == 10))) 
			 )
        {
            if(no<5)
            {
                alley.endDown();
            } 
            else
            {
                alley.endUp();
            }
        }
        while(!restoreFlags[no]){
           try{
                wait();
            }

           catch(InterruptedException e){System.out.print("-- AOgHILAKDBGAIBSDFA");}
        }
        //notify();
        restoreFlags[no] = false;
        removalFlags[no] = false;  
}
    
//    public synchronized void restoreCar(int no){
//        notifyAll();
//        //I have been removed but i am not the right care to be restored
//        while( removalFlags[no] && !restoreFlags[no]){
//            notify();
//            try{
//            wait();
//            }
//           catch(InterruptedException e){}
//        }
//        
//            
//            restoreFlags[no] = false;
//            removalFlags[no] = false;  
//        
//
//    }
    public synchronized void MarkCarForRemoval(int no){
        removalFlags[no] = true;
    
    }
    public synchronized void MarkCarForRestoration(int no){
        restoreFlags[no] = true;
    
    }
    public synchronized boolean getRemovalFlag(int no){
        return removalFlags[no];
    }
    public synchronized boolean getRestoreFlag(int no){
        return restoreFlags[no];
    }
    public synchronized static Workshop getInstance(){
        if (instance == null){
            instance = new Workshop();
        }
        return instance;
    }
}

class Field{
    private Alley alley = Alley.getInstance();
    private Workshop workshop = Workshop.getInstance();
	private static Field instance = null;
	int[][] fields;
	
	protected Field(int row,int col) {
		fields = new int[row][col];
		for(int i = 0 ; i < row ; i++) {
			for(int j = 0 ; j < col ; j++) {
				fields[i][j] = 10;
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
	

        
       
	public synchronized int checkNewPos(int no,CarDisplayI cd,Pos current,Pos newpos)throws InterruptedException {
			


            //Check if we are about to enter alley
	    if(( newpos.col == 0 && newpos.row == 2 && current.col != 0)|| 
	    	//( newpos.col == 0 && newpos.row == 11 && current.col != 0) || 
	    	( newpos.col == 0 && newpos.row == 10) || 
	    	(no == 3 && newpos.col == 3 && current.col == 4 && newpos.row == 1) || 
	    	(no == 4 && newpos.col == 3 && current.col == 4 && newpos.row == 1) ){
	        return 1;
	        
	    }
	    //check if the cars has left the alley//moved col when we implemented bridge to avoid deadlock 
	    if(((newpos.col == 2) && (current.col == 1) && (no < 5)||(no > 4)&& newpos.col == 2 && newpos.row == 0)){
	        return 2;
	        
	    }

        while(fields[newpos.row][newpos.col] != 10)
        {
        	try 
        	{
        		wait();

        	} catch (InterruptedException e) {throw e;}
       	}
        
       	fields[newpos.row][newpos.col] = no;
       	notifyAll();
       	return 0;
	}
       //Release the old field on the playground
   public void releaseOldPos(int row,int col) {
	   fields[row][col] =10;
   }
   public synchronized void setPlayfield(int no){
       for(int i = 0 ; i < 11 ; i++) {
    	   for(int j = 0 ; j < 12 ; j++) {
                   if(fields[i][j]== no){
                	   fields[i][j] = 10;
                   }
    	   }			
       }
       
   }
       
}