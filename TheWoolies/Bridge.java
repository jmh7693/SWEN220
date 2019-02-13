/*
 * Bridge.java
 *
 * Version:
 *   $Id$
 *
 * Revisions:
 *   $Log$
 */

import java.util.*;

/**
 * Simulation of the bridge troll controlling the passage of
 * pedestrians on the bridge crossing the Zyxnine River.
 *
 * This bridge troll will only allow one Woolie on the bridge at
 * a time.  Waiting Woolies are selected at random and allowed to
 * cross when the bridge is free.
 *
 * @author	Jim Vallino
 */

public class Bridge {
    
    private static int MAX_ON_BRIDGE = 1;  // Maximum number of Woolies
                                           // allowed on the bridge


    private int numOnBridge;  // The number of Woolies on the bridge

    /**
     * Constructor for the Bridge class.
     */

    public Bridge() {
        numOnBridge = 0;
    }

    /**
     *  Request permission to enter the bridge.
     */

    public synchronized void enterBridge() {
        // As long as there is no room for the Woolie on the
        // bridge, we have to wait.  Eventually the Woolie on the
        // bridge will cross and I will be notified.
        while(numOnBridge >= MAX_ON_BRIDGE)
            try{
                wait();
            }catch (InterruptedException e){
                e.printStackTrace();
            }
        // There is one more Woolie on the bridge
	   numOnBridge++;
	
    }
    
    /**
     *   Notify the bridge troll that a Woolie is leaving the bridge.
     */

    public synchronized void leaveBridge() {
	// Someone just left the bridge

	if ( numOnBridge > 0 ) {
            // One less Woolie on the bridge
	    numOnBridge--;

            // Wake up all the waiting Woolies and let the race
            // begin.  One of them will get the lock on enterBridge()
            // first.  
        notifyAll();
  
	    }
    }

} // Bridge