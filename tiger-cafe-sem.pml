//Foods a customer can order
mtype {CHILI, SANDWICH, PIZZA, NONE}; //NONE acts as a reset for new cust
mtype allFoods[4];
 
#define NCUST 3
#define NSERV 1
#define semaphore byte
 
 
/*
 * Mutex semaphores for all processes that access critical section
 * (any interaction in the Tiger Cafe)
 */
semaphore customerMutex[NCUST] = 1;
semaphore custMutex = 1;
semaphore cashierMutex = 1;
semaphore serverMutex[NSERV] = 1;
 
/*
 * Up and down functions on semaphores.
 * down blocks if the semaphore is 0 on entry to CS
 * up releases the hold on the CS
 */
inline up(s)    { s++ }
inline down(s)  { atomic{ s > 0 ; s-- } }
 


/*
 *Global definitions - 
 *Customer and cashier 
*/

/*
 *how we record new customers 
*/
bool customerInStore[NCUST] = false; 

/*
 *how the customer knows the cashier is ready to take order
*/
bool cashierBusy = false;

/*
 *how the cashier knows the customer is ready to order
*/
bool customerWaiting[NCUST] = false;

/*
 *how the customer knows that cashier is ready to take order
*/
bool custPlacedOrder[NCUST] = false;

/*
 *how we know customer has had order taken
*/
bool orderTaken[NCUST] = false;

/*
 *customer knows the cashier has selected a customers order
*/
bool someCustSelected = false;



/*
 * Global definitions - 
 * Cashier and Server
*/

mtype foodArray[4]; 

mtype customerOrder[NCUST];

bool custOrderSent[NCUST] = false;

bool serverBusy[NSERV] = false;


/*
 * Global definitions - 
 * Server and Customer
*/

/*
 * changes boolean when an order is fulfilled
 * and served
*/
bool orderFulfilled[NCUST] = false;
 


/*
 * Customer - takes in the customer's favoritve food and their id number, and runs that customer
 * through the cafe
*/
proctype Customer(mtype favFood, id) {
        do
        ::  customerWaiting[id] == false -> //initialize customer state
                printf("Customer %d enters store\n", id);
                custPlacedOrder[id] = false;
                orderFulfilled[id] = false;
                customerWaiting[id] = true;
                if
                :: !cashierBusy -> //wait for cashier to be ready
                        down(customerMutex[id]); //enter CS and place order
                        customerOrder[id] = foodArray[id];
                        printf("Customer %d tells Cashier he wants %e\n", id, foodArray[id]); //place order
                        custPlacedOrder[id] = true;
                        if
                        :: orderFulfilled[id] -> //wait for the order to be fulfilled
                                customerWaiting[id] = false;
                                custPlacedOrder[id] = false;
                                orderFulfilled[id] = false;
                                printf("C%d's order has been fulfilled and he leaves the restauraunt\n", id);
                                printf("--------------------------------------------------\n");
                                custOrderSent[id] = false;
                                orderTaken[id] = false;
                                customerOrder[id] = NONE;
                                someCustSelected = false;
                                up(customerMutex[id]);
                        fi;
                fi;
        od;
}


/*
 * Cashier - handles all operations for Cashier
*/
proctype Cashier() {
        bool someCustPlacedOrder = false;
        byte custID; //for iterator
        mtype custsOrder;
        do
        :: for (custID : 0 .. 2) { //search for waiting customers

                if 
                //if customer's waiting to order
                ::  customerWaiting[custID] && !custPlacedOrder[custID] && !someCustSelected ->
                        down(cashierMutex);
                        someCustPlacedOrder = true;
                        custOrderSent[custID] = false;
                        cashierBusy = false;
                        someCustSelected = true;
                        //printf("Cashier selects customer %d\n", custID);
                :: custPlacedOrder[custID] && !serverBusy[0] && !orderTaken[custID] ->
                        
                        orderTaken[custID] = true;
                        custOrderSent[custID] = true; //notify server of the customer order
                        printf("Cashier selects customer %d and takes his order of %e\n", custID, customerOrder[custID]);
                        printf("Cashier sends customer %d's order of %e to the server\n", custID, customerOrder[custID]);
                        custsOrder = foodArray[custID]; //take customer's order
                        up(cashierMutex);
                :: !someCustPlacedOrder && custID == 2 ->
                        printf("Cashier waits for a customer to approach him\n");
                :: else ->
                        skip;
                fi;
        }
        od;
}
 

/*
 * Server - handles all operations for Server
*/
proctype Server() {
        bool receivedOrder = false;
        byte custID;
        do
        :: for (custID : 0 .. 2) {
                if
                :: custOrderSent[custID] ->
                   down(serverMutex[0]);
                   receivedOrder = true;
                   serverBusy[0] = true;
                   printf("Server retrieves & creates customer %d's order of %e\n", custID, customerOrder[custID]);
                   printf("Server delivers customer %d his order of %e\n", custID, customerOrder[custID]);
                   orderFulfilled[custID] = true; //reset flag
                   up(serverMutex[0]);   
                   serverBusy[0] = false;
                   
                   cashierBusy = false; 
                   receivedOrder = false;
                :: !custOrderSent[0] && ! custOrderSent[1] && !custOrderSent[2] -> //!receivedOrder && custID == 2-> (same id number)
                   printf("Server waits for an order to come in\n");
                :: else ->
                        skip;
                fi;
        }
        od;
}
 

init {
    atomic {
        foodArray[0] = CHILI;
        foodArray[1] = SANDWICH;
        foodArray[2] = PIZZA;
        foodArray[3] = NONE;
        run Customer(CHILI, 0);
        run Customer(SANDWICH, 1);
        run Customer(PIZZA, 2);
        run Cashier();
        run Server();
    }
}



ltl Safety {
        [] customerWaiting[2] && ! cashierBusy -> customerOrder[2] == PIZZA
}

ltl Liveness {
        [] customerWaiting[2] -> <> custPlacedOrder[2]
}