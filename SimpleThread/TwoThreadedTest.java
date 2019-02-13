

public class TwoThreadedTest {

	    public static void main (String[] args) {
	    	SimpleThreaded simpleOne = new SimpleThreaded("Jamaica");
	        SimpleThreaded simpleTwo = new SimpleThreaded("Fiji");
	        simpleOne.start();
	        simpleTwo.start();
	    }
	}


