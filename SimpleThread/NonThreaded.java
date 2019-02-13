public class NonThreaded {
private String name = null;

public NonThreaded(String str) {
	name = str ;
}
public void run() {
    for (int i = 0; i < 10; i++) {
        System.out.println(i + " " + name );
    }
    System.out.println("DONE! " + name );
    }
}

