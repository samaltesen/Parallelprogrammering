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
	
	Alley alley;
	Field field;
	Pos oldPos;
	

    int basespeed = 100;             // Rather: degree of slowness
    int variation =  50;             // Percentage of base speed

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
    	
    	alley = Alley.getAlley();
        field = Field.getField();
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
    
    void checkPos(Pos pos, int no) throws InterruptedException 
    {
    	if(alley.enteringAlley(pos, no)) 
    	{
    		alley.enter(no);
    	} 
    	else if(alley.leavingAlley(pos, no)) 
    	{
    		alley.leave(no);
    	}
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
                
                checkPos(newpos, no);
                field.takePos(newpos);
                
                //  Move to new position 
                cd.clear(curpos);
                cd.mark(curpos,newpos,col,no);
                sleep(speed());
                cd.clear(curpos,newpos);
                cd.mark(newpos,col,no);

                oldPos = curpos;
                curpos = newpos;
                
                
                field.releasePos(oldPos);
                
            }

        } catch (Exception e) {
            cd.println("Exception in Car no. " + no);
            System.err.println("Exception in Car no. " + no + ":" + e);
            e.printStackTrace();
        }
    }

}

public class CarControl implements CarControlI{

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
    }

    public void stopCar(int no) {
        gate[no].close();
    }

    public void barrierOn() { 
        cd.println("Barrier On not implemented in this version");
    }

    public void barrierOff() { 
        cd.println("Barrier Off not implemented in this version");
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

class Alley {

	private static Alley alley = null;
	private int carsUp = 0;
	private int carsDown = 0;
	
	public Alley() {
		
	}
	
	public static Alley getAlley() {
		if(alley == null) {
			alley = new Alley();
		}
		return alley;
	}
	
	public synchronized void enter(int no)
	{
		
		
		if(no <= 4) 
		{
			while(carsUp > 0) 
			{
				try
				{
	               wait();
				} catch(InterruptedException e) {}
			}
			carsDown++;
			notify();
			
		}
		else 
		{
			while(carsDown > 0) 
			{
		           
				try
				{
	               wait();
				} catch(InterruptedException e) {}
	        		   
			}
			
			carsUp++;
			notify();
		}
		
		System.out.println("Car no ENTER " + no + " cars up " + carsUp + " carsDown " + carsDown);
		
	}
	

	public synchronized void leave(int no) throws InterruptedException
	{
		if(no <= 4)
		{
			carsDown--;
			if(carsDown == 0) {
				notify();
			}
		}
		else
		{
			carsUp--;
			if(carsUp == 0) {
				notify();
			}
		}
		
		System.out.println("Car no LEAVE " + no + " cars up " + carsUp + " carsDown " + carsDown);
	}

	
	public boolean enteringAlley(Pos pos, int no) {
		
		if( no <= 2 && pos.col == 0 && pos.row == 2) 
		{
			return true;
		}
		else if(no <= 4 && pos.col == 2 && pos.row == 1) 
		{
			return true;
		}
		else if(no <= 8 && pos.col == 0 && pos.row == 10) 
		{
			return true;
		}
		
		return false;
	}
	
	public boolean leavingAlley(Pos pos, int no) {
		
		if( no <= 4 && pos.col == 1 && pos.row == 9) 
		{
			return true;
		}
		else if(no <= 8 && pos.col == 2 && pos.row == 0) 
		{
			return true;
		}

		return false;
	}
	
}

class Field {
	
	private static Field f = null; 
	Semaphore[][] field;
	
	public Field() {
		
		field = new Semaphore[11][12];
		for(int i=0; i < 11; i++) {
			for(int j = 0; j < 12; j++) {
				field[i][j] = new Semaphore(1);
			}
		}
	}
	
	public static Field getField() {
		if(f == null) {
			f = new Field();
		}
		return f;
	}
	
	public void takePos(Pos pos) throws InterruptedException {
		field[pos.row][pos.col].P();
	}
	
	public void releasePos(Pos pos) {
		field[pos.row][pos.col].V();
	}
	
	
	
}






