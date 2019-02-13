/*
 * Woolie.java
 *
 * Version:
 *   $Id$
 *
 * Revisions:
 *   $Log$
 */

/**
 * Woolie - simulates a woolie crossing a bridge
 * <p>
 * Each woolie object is constructed with a name, length of time it
 * takes the woolie to cross the bridge, and a destination city.  Woolie
 * objects extend the Thread class and execute as an individual thread.
 *
 * Before crossing the bridge, a Woolie will ask a bridge troll for
 * permission to cross.  Once the bridge troll grants permission, the
 * Woolie crosses the bridge.  Once on the other side, the Woolie will
 * notify the troll that they have left the bridge.
 *
 * @author      Jim Vallino
 */
public class Woolie extends Thread {
    private String name;         // The name of this Woolie
    private int crossingTime;    // The number of seconds require to cross
    private String destination;  // The name of the destination of this Woolie

    private Bridge theTroll;     // The bridge the Woolie will cross
    
    /**
     * Construct a new Woolie object that can be started in a separate
     * thread.  The constructor will simply initialize all of the 
     * instance fields.
     *
     * @param       myName          the name of this Woolie
     * @param       myCrossingTime  the number of seconds it takes the Woolie 
     *                              to cross the bridge
     * @param       myDestination   the city the Woolie is heading to
     * @param       theBridge       the bridge the Woolie is crossing
     */

    public Woolie( String myName, int myCrossingTime, String myDestination, 
                   Bridge theBridge ) {
	name = myName;
	crossingTime = myCrossingTime;
	destination = myDestination;
        theTroll = theBridge;
    }
    
    /**
     * This method handles the Woolie's crossing of the bridge.  There
     * are several message that must be displayed to describe the Woolie's
     * progress crossing the bridge.  <I>Note: In all the following
     * messages</I>
     * <code>name</code> <I>is the name of the Woolie.</I>
     *
     * <ul>
     * <li>When the Woolie thread starts, the message<br>
     * <blockquote><code> name has arrived at the bridge.</code></blockquote>
     * is displayed.
     * <li>When the Woolie starts crossing the bridge, at time 0, the message
     * <br>
     * <blockquote><code> name is starting to cross.</code></blockquote>
     * is displayed.
     * <li>For every one second interval, beyond time 0, that the Woolie is on 
     * the bridge a message<br>
     * <blockquote><code> "tab" name x seconds.</code></blockquote>
     * should be printed where <code>x</code>
     * is the number of seconds that the Woolie has been on the bridge and "tab" is the tab character - '\t'.
     * <li>When the Woolie reaches his or her destination display the
     * message<br>
     * <blockquote><code> name leaves at city.</code></blockquote>
     * where <code>city</code> is the Woolie's destination.
     * </ul>
     */

    public void run() {

        // The Woolie has started to cross the bridge

	System.out.println(name + " has arrived at the bridge.");

        // Get permission to cross from the troll

        theTroll.enterBridge();

        // Simulate the time on the bridge

	for ( int time = 0; time < crossingTime; time++ ) {
            // Take care of output

	    if( time == 0 )
		System.out.println( name + " is starting to cross." );
	    else
		System.out.println( "\t" + name + ' ' + time + " seconds." );

            // Let time pass

	    try {
		sleep(1000);
	    }
	    catch( InterruptedException e ) {}
	}

        // Tell the troll we have crossed

        theTroll.leaveBridge();

        // Finished crossing

	System.out.println( name + " leaves at " + destination + "." );
    }

} // Woolie