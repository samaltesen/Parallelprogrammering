
import static java.lang.Math.random;
import java.util.Random;

//Prototype implementation of Car Test class
//Mandatory assignment
//Course 02158 Concurrent Programming, DTU, Fall 2017

//Hans Henrik Lovengreen     Oct 9, 2017

public class CarTest extends Thread {

    CarTestingI cars;
    int testno;

    public CarTest(CarTestingI ct, int no) {
        cars = ct;
        testno = no;
    }

    public void run() {
        try {
            switch (testno) { 
            case 0:
                // Demonstration of startAll/stopAll.
                // Should let the cars go one round (unless very fast)
                cars.startAll();
                sleep(3000);
                cars.stopAll();
                break;
            case 1:
                //test the barriere
                cars.startAll();
                for(int i = 1000 ; i<5000;i = i+1000){
                    sleep(i);
                    cars.barrierOn();
                    sleep(i);
                    cars.barrierOff();
                }
                cars.stopAll();
                break;
            case 2:
                //test the bridge
                cars.startAll();
                cars.setLimit(2);
                sleep(5000);
                cars.setLimit(4);
                sleep(8000);
                cars.setLimit(2);
                sleep(5000);
                break;
            case 3:
                //random stop 
                cars.startAll();
                Random r = new Random();
                int test;
                   for(int i = 0 ; i < 10 ; i++){
                       test = r.nextInt(9);
                       sleep(4000);
                       cars.removeCar(test);
                       sleep(4000);
                       cars.restoreCar(test);
                       
                   } 
                cars.stopAll();
                break;
            case 4:
                cars.startAll();
                Random r2 = new Random();
                sleep(2000);
                
                   for(int i = 0 ; i < 10 ; i++){
                       test = r2.nextInt(9);
                       cars.removeCar(test);
                       cars.restoreCar(test);
                       sleep(500);
                   }
                   cars.stopAll();
                
            case 19:
                // Demonstration of speed setting.
                // Change speed to double of default values
                cars.println("Doubling speeds");
                for (int i = 1; i < 9; i++) {
                    cars.setSpeed(i,50);
                };
                break;

            default:
                cars.println("Test " + testno + " not available");
            }

            cars.println("Test ended");

        } catch (Exception e) {
            System.err.println("Exception in test: "+e);
        }
    }

}



