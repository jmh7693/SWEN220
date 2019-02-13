/*
 * TestTroll.java
 *
 * Version:
 *   $Id$
 *
 * Revisions:
 *   $Log$
 */

/**
 * Test the Troll by creating a bunch of Woolies and let them cross.
 * If things are working correctly, only one Woolie will be on the
 * bridge at a time.
 *
 * @author     Jim Vallino
 */
public class TestTroll {

    /**
     * Create a bunch of Woolies and let them cross the bridge.
     *
     * @param args[] command line arguments (ignored)
     */

    public static void main( String args[] ) {
        // Here come the Woolies...
        // Create a bridge troll

        Bridge troll = new Bridge();


	Thread ped1 = new Woolie( "Jim", 3, "Merctran", troll );
	Thread ped2 = new Woolie( "Paul", 5, "Merctran", troll );
	Thread ped3 = new Woolie( "H-P", 10, "Sicstine", troll );
	Thread ped4 = new Woolie( "Karen", 4, "Sicstine", troll );
	Thread ped5 = new Woolie( "Edith", 6, "Sicstine", troll );

        // Run them

	try {
	    ped1.start();
	    Thread.currentThread().sleep(500);

	    ped2.start();
	    Thread.currentThread().sleep(500);

	    ped3.start();
	    Thread.currentThread().sleep(500);

	    ped4.start();
	    Thread.currentThread().sleep(500);

	    ped5.start();
	}
	catch(InterruptedException e) {}
	
    }
}