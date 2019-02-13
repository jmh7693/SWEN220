

public class TwoNonThreadedTest {

	    public static void main (String[] args) {
	    	NonThreaded simpleOne = new NonThreaded("Jamaica");
	        NonThreaded simpleTwo = new NonThreaded("Fiji");
	        simpleOne.run();
	        simpleTwo.run();
	    }
	}


