byte lcm = 0 ;
byte gcd = 0 ;

proctype LCM( byte ox ; byte oy ) {
	//variable declarations used by proc
	byte temp = 0 ;
	byte x = ox ;
	byte y = oy ;

	//do loop for determing lcm of input
	do
	:: x > y -> temp = y ; y = x - y ; x = temp ;
	:: x < y -> temp = x ; x = y - x ; y = temp ;
	:: x == y -> break ;
	od ;
	
	gcd = x ;

	lcm = (ox*oy)/gcd ;
	
	printf("***LCM of %d and %d is %d\n", ox, oy, lcm) ;
}

init {
	// should print 20
	run LCM(20, 10) ;
}