/*
 * Number of equipment pieces made in a days worth of work.
 */
#define DAYSWORK 8

/*
 * Capacity of each channel (equipment or messages).
 */
#define CAPACITY 2

/*
 * Types of electronic equipment produced.
 */
mtype = {DOMESTIC, INTERNATIONAL} ;

/*
 * Stop message.
 */
mtype = {STOP} ;

/*
 * Channels to pass equipment and messages from place to place.
 */
chan ManufacturerToDistributer  = [CAPACITY] of {mtype} ;
chan DistributerToDomestic      = [CAPACITY] of {mtype} ;
chan DistributerToInternational = [CAPACITY] of {mtype} ;

/*
 * Inline procedure to choose an equipment type and
 * assign it to mtype parameter 'product'
 *
 * USE THIS WHERE REQUIRED IN THE MANUFACTURER PROCESS
 */
inline choose(product) {
    if
    :: product = DOMESTIC ;
    :: product = INTERNATIONAL ;
    fi;
}

/*
 * The Manufacturer process.
 */
active proctype Manufacturer() {
    byte next_product = STOP ;
    byte equipment_count = 0 ;

	do
	::	
		if
		:: equipment_count < DAYSWORK ->
			choose(next_product) ;
			printf("Manufactured a new %e equipment \n", next_product) ;
			equipment_count++ ;
			ManufacturerToDistributer ! next_product ;

		:: else ->
			printf("Manufacture done \n") ;
			ManufacturerToDistributer ! STOP ;
			break ;		
		fi;
	od;
}

/*
 * The Distributer process
 */
active proctype Distributer() {
    byte domestic_count = 0 ;
    byte international_count = 0 ;
	
	do
		:: ManufacturerToDistributer ? DOMESTIC ->
			printf("Distribute receives Domestic product \n") ;
			domestic_count++ ;
			DistributerToDomestic ! DOMESTIC ;
    	:: ManufacturerToDistributer ? INTERNATIONAL ->
			printf("Distribute receives International product \n") ;
			international_count++ ;
			DistributerToInternational ! INTERNATIONAL ;

		:: ManufacturerToDistributer ? STOP ->
			printf("Distributer is done after %d domestic and %d international pieces \n", domestic_count, international_count) ;
			DistributerToDomestic ! STOP ;
			DistributerToInternational ! STOP ;
			break ;
	od;
}

/*
 * The Domestic Warehouse process
 */
active proctype Domestic() {
    byte piece_count = 0 ;

    do
	:: 
		if
		:: DistributerToDomestic ? DOMESTIC ->
			piece_count++ ;
			printf("Domestic warehouse receives another piece \n") ;
		:: DistributerToDomestic ? STOP ->
			printf("Domestic warehouse closes after receiving %d pieces \n", piece_count) ;
			break ;
		fi;
	od;	
}

/*
 * The International Warehouse process
 */
active proctype International() {
    byte piece_count = 0 ;

    do
	:: 
		if
		:: DistributerToInternational ? INTERNATIONAL ->
			piece_count++ ;
			printf("International warehouse receives another piece \n") ;
		:: DistributerToInternational ? STOP ->
			printf("International warehouse closes after receiving %d pieces \n", piece_count) ;
			break ;
		fi;
	od;
}




