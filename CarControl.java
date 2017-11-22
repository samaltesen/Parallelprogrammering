//Prototype implementation of Car Control
//Mandatory assignment
//Course 02158 Concurrent Programming, DTU, Fall 2017

//Hans Henrik Lovengreen     Oct 9, 2017

import java.awt.Color;

enum InterruptState{NOT_MOVED, MOVED, MIDDLE_OF_MOVE;}

class Gate
{

	Semaphore g = new Semaphore(0);
	Semaphore e = new Semaphore(1);
	boolean isopen = false;

	public void pass() throws InterruptedException
	{
		g.P();
		g.V();
	}

	public void open()
	{
		try
		{
			e.P();
		} catch (InterruptedException e)
		{
		}
		if (!isopen)
		{
			g.V();
			isopen = true;
		}
		e.V();
	}

	public void close()
	{
		try
		{
			e.P();
		} catch (InterruptedException e)
		{
		}
		if (isopen)
		{
			try
			{
				g.P();
			} catch (InterruptedException e)
			{
			}
			isopen = false;
		}
		e.V();
	}

}

class Car extends Thread
{

	Alley alley;
	Field field;
	Barrier barrier;
	Bridge bridge;
	Pos oldPos;
	InterruptState state;

	int basespeed = 100; // Rather: degree of slowness
	int variation = 50; // Percentage of base speed

	CarDisplayI cd; // GUI part

	int no; // Car number
	Pos startpos; // Startpositon (provided by GUI)
	Pos barpos; // Barrierpositon (provided by GUI)
	Color col; // Car color
	Gate mygate; // Gate at startposition

	int speed; // Current car speed
	Pos curpos; // Current position
	Pos newpos; // New position to go to

	public Car(int no, CarDisplayI cd, Gate g)
	{

		alley = Alley.getAlley();
		field = Field.getField();
		barrier = Barrier.getBarrier();
		bridge = Bridge.getInstance();
		state = InterruptState.NOT_MOVED;
		
		this.no = no;
		this.cd = cd;
		mygate = g;
		startpos = cd.getStartPos(no);
		barpos = cd.getBarrierPos(no); // For later use

		col = chooseColor();

		// do not change the special settings for car no. 0
		if (no == 0)
		{
			basespeed = 0;
			variation = 0;
			setPriority(Thread.MAX_PRIORITY);
		}
	}

	public synchronized void setSpeed(int speed)
	{
		if (no != 0 && speed >= 0)
		{
			basespeed = speed;
		} else
			cd.println("Illegal speed settings");
	}

	public synchronized void setVariation(int var)
	{
		if (no != 0 && 0 <= var && var <= 100)
		{
			variation = var;
		} else
			cd.println("Illegal variation settings");
	}

	synchronized int chooseSpeed()
	{
		double factor = (1.0D + (Math.random() - 0.5D) * 2 * variation / 100);
		return (int) Math.round(factor * basespeed);
	}

	private int speed()
	{
		// Slow down if requested
		final int slowfactor = 2;
		return speed * (cd.isSlow(curpos) ? slowfactor : 1);
		//return slowfactor*speed;
	}

	Color chooseColor()
	{
		return Color.blue; // You can get any color, as longs as it's blue
	}

	Pos nextPos(Pos pos)
	{
		// Get my track from display
		return cd.nextPos(no, pos);
	}

	boolean atGate(Pos pos)
	{
		return pos.equals(startpos);
	}

	void checkNewPos(Pos pos, int no) throws InterruptedException
	{
		//System.out.println("Car no " + no + " testing at position row " + pos.row + " and column " + pos.col );
		if (alley.enteringAlley(pos, no))
		{
			alley.enter(no);
		} 
		
		if (barrier.getState() && barrier.atBarrier(pos, no))
		{
			barrier.sync();
		} 
		
		if (bridge.enteringBridge(pos, no))
		{
			bridge.enter(no);
		} 
		
	}

	void checkOldPos(Pos pos, int no) throws InterruptedException 
	{
		if (alley.leavingAlley(pos, no))
		{
			alley.leave(no);
		} 
		
		if (bridge.leavingBridge(pos, no)) 
		{
			bridge.leave(no);
		}
		
	}
	public void run()
	{
		try
		{

			speed = chooseSpeed();
			curpos = startpos;
			cd.mark(curpos, col, no);

			while (true)
			{
			
					state = InterruptState.NOT_MOVED;
					sleep(speed());
	
					if (atGate(curpos))
					{
						mygate.pass();
						speed = chooseSpeed();
					}
	
					newpos = nextPos(curpos);
	
					checkNewPos(newpos, no);
					field.takePos(newpos);
	
					// Move to new position
					cd.clear(curpos);
					cd.mark(curpos, newpos, col, no);

					state = InterruptState.MIDDLE_OF_MOVE;
					sleep(speed());
					cd.clear(curpos, newpos);
					cd.mark(newpos, col, no);
	
					oldPos = curpos;
					curpos = newpos;
	
					checkOldPos(oldPos, no); 
					field.releasePos(oldPos);
				
			} 

		}
		catch(InterruptedException e) 
		{ 
			if(state == InterruptState.NOT_MOVED) {
				cd.clear(curpos);
				field.releasePos(curpos);
			} else if(state == InterruptState.MIDDLE_OF_MOVE)
			{
				cd.clear(curpos);
				cd.clear(newpos);
				field.releasePos(curpos);
				field.releasePos(newpos);
			}
			
			if(alley.isCarInAlley(no)) {
				try
				{
					alley.leave(no);
				} catch (InterruptedException e1)
				{
					// TODO Auto-generated catch block
					e1.printStackTrace();
				}
			}
		}
		catch (Exception e)
		{
			cd.println("Exception in Car no. " + no);
			System.err.println("Exception in Car no. " + no + ":" + e);
			e.printStackTrace();
		}
	}

}

public class CarControl implements CarControlI
{

	CarDisplayI cd; // Reference to GUI
	Car[] car; // Cars
	Gate[] gate; // Gates
	Barrier barrier;
	Bridge bridge;
	Alley alley;

	public CarControl(CarDisplayI cd)
	{
		this.cd = cd;
		car = new Car[9];
		gate = new Gate[9];
		barrier = Barrier.getBarrier();
		bridge = Bridge.getInstance();
		alley = Alley.getAlley();
		for (int no = 0; no < 9; no++)
		{
			gate[no] = new Gate();
			car[no] = new Car(no, cd, gate[no]);
			car[no].start();
		}
	}

	public void startCar(int no)
	{
		gate[no].open();
	}

	public void stopCar(int no)
	{
		gate[no].close();
	}

	public void barrierOn()
	{
		barrier.on();
		//cd.println("Barrier On not implemented in this version");
	}

	public void barrierOff()
	{
		barrier.off();
		//cd.println("Barrier Off not implemented in this version");
	}

	public void barrierShutDown()
	{
		barrier.shutdown();
		//cd.println("Barrier shut down not implemented in this version");
		// This sleep is for illustrating how blocking affects the GUI
		// Remove when shutdown is implemented.
		//try
		//{
		//	Thread.sleep(3000);
		//} catch (InterruptedException e)
		//{
		//}
		// Recommendation:
		// If not implemented call barrier.off() instead to make graphics
		// consistent
	}

	public void setLimit(int k)
	{     
		bridge.setLimit(k);
		//cd.println("Setting of bridge limit not implemented in this version");
	}

	public void removeCar(int no)
	{
		boolean test = car[no].isAlive();
		if(test) 
		{	
			car[no].interrupt();
		}
		
		//cd.println("Remove Car not implemented in this version");
	}

	public void restoreCar(int no)
	{
		if(!car[no].isAlive()) 
		{
			car[no] = new Car(no, cd, gate[no]);
			car[no].start();
			
		}
		cd.println("Restore Car not implemented in this version");
	}

	/* Speed settings for testing purposes */

	public void setSpeed(int no, int speed)
	{
		car[no].setSpeed(speed);
	}

	public void setVariation(int no, int var)
	{
		car[no].setVariation(var);
	}

}

class Alley
{

	private static Alley alley = null;
	private int carsUp = 0;
	private int carsDown = 0;
	private int[] carsInAlley = new int[9];

	public Alley()
	{

	}

	public static Alley getAlley()
	{
		if (alley == null)
		{
			alley = new Alley();
		}
		return alley;
	}

	public synchronized void enter(int no) throws InterruptedException
	{

		if (no <= 4)
		{
			while (carsUp > 0)
			{
				
					wait();
				
			}
			carsDown++;
			carsInAlley[no] = no;
			notify();

		} else
		{
			while (carsDown > 0)
			{

				
					wait();
				

			}
			carsInAlley[no] = no;
			carsUp++;
			notify();
		}

	}

	public synchronized void leave(int no) throws InterruptedException
	{
		if (no <= 4)
		{
			carsDown--;
			carsInAlley[no] = 0;
			if (carsDown == 0)
			{
				notify();
			}
		} else
		{
			carsUp--;
			carsInAlley[no] = 0;
			if (carsUp == 0)
			{
				notify();
			}
		}

	}

	public boolean enteringAlley(Pos pos, int no)
	{

		if (no <= 2 && pos.col == 0 && pos.row == 2)
		{
			return true;
		} else if (no <= 4 && pos.col == 2 && pos.row == 1)
		{
			return true;
		} else if (no <= 8 && pos.col == 0 && pos.row == 10)
		{
			return true;
		}

		return false;
	}

	public boolean leavingAlley(Pos pos, int no)
	{

		if (no <= 4 && pos.col == 1 && pos.row == 9)
		{
			return true;
		} else if (no <= 8 && pos.col == 2 && pos.row == 0)
		{
			return true;
		}

		return false;
	}
	
	public boolean isCarInAlley(int no) 
	{
		
		for(int i = 0; i < 9; i++) 
		{
			if(carsInAlley[i] == no) 
			{
				return true;
			}
		}
		
		return false;
	}

	public int getCarsDown()
	{
		return carsDown;
	}

	
}

class Field
{

	private static Field f = null;
	Semaphore[][] field;

	public Field()
	{

		field = new Semaphore[11][12];
		for (int i = 0; i < 11; i++)
		{
			for (int j = 0; j < 12; j++)
			{
				field[i][j] = new Semaphore(1);
			}
		}
	}

	public static Field getField()
	{
		if (f == null)
		{
			f = new Field();
		}
		return f;
	}

	public void takePos(Pos pos) throws InterruptedException
	{
		field[pos.row][pos.col].P();
	}

	public void releasePos(Pos pos)
	{
		field[pos.row][pos.col].V();
	}

}

class Barrier
{
	private static Barrier b = null;
	private int carsWaiting;
	private boolean barrierState;

	public Barrier()
	{
		carsWaiting = 0;
		barrierState = false;
	}

	public static Barrier getBarrier()
	{
		if (b == null)
		{
			b = new Barrier();
		}
		return b;
	}

	public synchronized void on()
	{
		barrierState = true;
	}

	public synchronized void off()
	{
		barrierState = false;
		if (carsWaiting > 0)
		{
			carsWaiting = 0;
			notifyAll();
		}
	}

	public synchronized void shutdown()
	{

		while (carsWaiting != 0)
		{
			try
			{
				wait();
			} catch (InterruptedException e)
			{
			}
		}

		barrierState = false;

	}

	public synchronized void sync()
	{
		carsWaiting++;
		if (carsWaiting == 9)
		{
			carsWaiting = 0;
			notifyAll();
		} else
		{
			try
			{
				wait();
			} catch (InterruptedException e)
			{
			}
		}

	}

	public boolean atBarrier(Pos pos, int no)
	{
		if (no <= 4 && pos.row == 5 && pos.col > 2)
		{
			return true;
		} else if (pos.row == 6 && pos.col > 7)
		{
			return true;
		}

		return false;
	}

	public boolean getState()
	{
		return barrierState;
	}

}

class Bridge
{
	private Alley alley = Alley.getAlley();
	private int limit = 6;
	private int counter = 0;
	private static Bridge instance = null;

	public synchronized void enter(int no)
	{

		while (counter == limit)
		{
			try
			{
				wait();
			} catch (InterruptedException e)
			{

			}
		}
		while (limit < 5 && alley.getCarsDown() > 0 && counter == limit - 1 && no > 4)
		{
			notify();
			try
			{
				wait();
			} catch (InterruptedException e)
			{

			}
		}

		counter++;

	}

	public synchronized void leave(int no)
	{
		counter--;
		notify();
	}

	public void setLimit(int k)
	{
		limit = k;

	}

	public static Bridge getInstance()
	{
		if (instance == null)
		{
			instance = new Bridge();
		}
		return instance;
	}

	public boolean enteringBridge(Pos pos, int no)
	{
		if(pos.row > 7) 
		{
			if (no <= 4 && pos.col == 1)
			{
				return true;
			}
			else if (pos.col == 3 && pos.row == 10)
			{
				return true;
			}
		}
		
		return false;
	}
	
	public boolean leavingBridge(Pos pos, int no)
	{
		if(pos.row > 8) 
		{
			if (no <= 4 && pos.col == 4)
			{
				return true;
			}
			else if (pos.col == 0 && pos.row == 10)
			{
				return true;
			}
		}
		
		return false;
	}
}


