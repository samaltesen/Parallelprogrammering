//Specification of Car Testing interface 
//Mandatory assignment
//Course 02158 Concurrent Programming, DTU, Fall 2017

//Hans Henrik Lovengreen     Oct 9, 2017


interface CarTestingI {
    /*
     * The test methods must be called sequentially. 
     * startBarrierShutDown() and awaitBarrierShutDown() must alternate and
     * barrierOn() and barrierOff() must not be called inbetween these.
     * Otherwise the methods may be called in any order. 
     */   
                                             // Corresponding GUI event

    public void startCar(int no);             // Click at red   gate no.
    public void stopCar(int no);              // Click at green gate no.

    public void startAll();                   // Click at Start All button
    public void stopAll();                    // Click at Stop  All button

    public void removeCar(int no);            // Click+shift at gate no.
    public void restoreCar(int no);           // Click+ctr   at gate no.

    public void barrierOn();                  // Click on On button
    public void barrierOff();                 // Click on Off button
    public void startBarrierShutDown();       // Click on Shut down button
    public void awaitBarrierShutDown();       // Wait for shut down to have completed

    public void setLimit(int k);              // Set bridge limit value

    public void setSlow(boolean slowdown);    // Set slow-down
    public void println(String message);      // Print (error) message on GUI

    public void setSpeed(int no, int speed);  // Set base speed (no GUI)
    public void setVariation(int no,int var); // Set variation  (no GUI)
}

