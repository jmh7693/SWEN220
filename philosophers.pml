/*  Dinning Philosophers Activity
 *
 *  Modify this model to prevent deadlock
 *  by having half the philosophers first
 *  reach for their right fork, and the other
 *  half reach for their left fork first.
 *
 *  This should break the cyclic hold and wait
 *  condition which is causing deadlock.
*/

/*
 * Number of processes, including init.
 */
#define NPROC 4

/*
 * want_to_eat[i] is true <-> philospher with pid = i wants
 * two forks to eat.
 */
bool want_to_eat[NPROC] = false ;

/*
 * eating[i] is true <-> philosopher with pid = i has both
 * forks and is eating.
 */
bool eating[NPROC] = false ;

/*
 * Pseudo-type semaphore
 */
#define semaphore byte

/*
 * Forks - each fork *is* a mutual exclusion semaphore
 */
semaphore fork[NPROC] = 1 ;

/*
 * Up (unlock) and down (lock) functions on semaphores.
 * down blocks if the semaphore is 0 on entry.
 */
inline up(s)    { s++ }
inline down(s)  { atomic{ s > 0 ; s-- } }

/*
 * Forever process (4 copies)
 */
active[4] proctype Phil() {
    byte me = _pid ;

	// lefty?
	bool lefty = me % 2;


	do
	::
		/*
		 * Thinking - Non-Critical Sectio
		 */
		printf("P%d is thinking\n", me) ;

	    /*
         * Get The Forks - Enter the Critical Section
         */
        want_to_eat[me] = true;
		printf("P%d wants to chow down\n", me);

		if
		:: lefty ->
			down(fork[me]);
			down(fork[ (me + 1) % NPROC ]);
		:: else ->
			down(fork[ (me + 1) % NPROC ]);
			down(fork[me]);
		fi;

        want_to_eat[me] = false ;

		/*
	     * Eating - Executing in the Critical Section
		 */
		eating[me] = true ;
        printf("P%d eating\n", me) ;
		eating[me] = false ;

		/*
		 * Give Back The Forks - Leave the Critical Section
		 */
         up(fork[me]) ;
		 up(fork[ (me + 1) % NPROC ]) ;
	od
}