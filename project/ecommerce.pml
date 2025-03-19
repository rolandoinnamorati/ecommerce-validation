#define DATABASE_SIZE 3
#define CHANNEL_SIZE 3
#define MAX_ELAPSED_TIME 5
#define POSSIBLE_ANOMALIES 5

#define CUSTOMER_NUMBER 2
#define PRODUCER_NUMBER 2
#define SHIPPER_NUMBER 2

//Structure to represent the actors. Type 0 for Customers, 1 for Producers, 2 for Shippers
typedef Actor {
	int id;
	int type;
	int descr;
}

//Structure to represent the items
typedef Item {
	int id;
	byte descr;
	int producer_id;
	int how_many;
	int how_many_min;
	bit producing;
}

//Structure to represent the orders
typedef Order {
	int id;
	int customer_id;
	int item_id;
	int how_many;
	int date_placed;
	int date_processed;
	int date_ready;
	int date_shipped;
	int date_arrived;
}

Actor actors[DATABASE_SIZE];
Item items[DATABASE_SIZE];
Order orders[DATABASE_SIZE];

int anomalies[POSSIBLE_ANOMALIES];
int time = 0;

//Channel in common where clients ask. Params: type, customer id, item id, quantity
chan CO = [CHANNEL_SIZE] of { bit, int, int, int };

//Dedicated channel where clients receive the response. Params: type, element id, description, how many
chan CI[CUSTOMER_NUMBER] = [CHANNEL_SIZE] of { bit, int, int, int };

//Channel in common where producers answer. Params: type, item id, quantity
chan PO = [CHANNEL_SIZE] of { int, int, int, int };

//Dedicated channel where producers receive the response. Params: type, producer id, item id, quantity
chan PI[PRODUCER_NUMBER] = [CHANNEL_SIZE] of { bit, int, int };

//Channel in common where shippers answer. Params: shipper id, order id, item id
chan SO = [CHANNEL_SIZE] of { bit, int, int };

//Dedicated channel where shippers receive the response. Params: order id, item id, quantity
chan SI[SHIPPER_NUMBER] = [CHANNEL_SIZE] of { int, int, int };


//Utility per generare numeri casuali
chan randomChan = [0] of { bit };
bit fd = 0;
bit fa = 0;
proctype RandomGenerator() {
    do
    :: randomChan!0
    :: randomChan!1
    od;
}

// Algorithm 1: Environment Setup
proctype EnvGen(byte p) {
    int n = 0;
    bit stop;
    int new_pid;
    bit rand_val;

    do
    :: (p == 0 && n > 0) -> // Caso: un cliente termina
        n--;
    :: (n >= 1 && n < DATABASE_SIZE) ->
        randomChan?rand_val;
        if
        :: (rand_val > fd) -> // Rimozione casuale
            stop = 0;
            do
            :: (stop == 0 && n > 0) ->
                new_pid = n - 1;
                actors[new_pid].id = -1; // Segna come terminato
                n--;
                stop = 1;
            :: else -> break;
            od;
        fi;
    :: (n < 1 || (n < DATABASE_SIZE)) ->
        randomChan?rand_val;
        if
        :: (rand_val > fa) -> // Creazione nuovo processo
            stop = 0;
            do
            :: (stop == 0 && n < DATABASE_SIZE) ->
                new_pid = n;
                actors[new_pid].id = new_pid;
                actors[new_pid].type = p;
                n++;
                stop = 1;
            :: else -> break;
            od;
        fi;
    :: else -> skip;
    od;
}

// Algorithm 2: Environment: single customer issuing requests
proctype Customer(int pid_cust) {
 	int elem_id, descr, how_many;
	int selected, quantity;

	CO!0, pid_cust, 0, 0;
	do
    	:: CI[pid_cust]?0, elem_id, descr, how_many
        		do
        		:: (how_many > 0) ->
            			if
            			:: skip -> selected = 0;
            			:: skip -> selected = 1;
            			fi
            			if
            			:: (selected == 1) ->
             				do
				:: quantity < how_many ->
					quantity++;
				:: break;
				od
                				CO!1, pid_cust, elem_id, quantity;
				CI[pid_cust]?1, elem_id, descr, how_many;
            			:: else -> skip;
            			fi
		:: else -> break;
        		od
	od
}

// Algorithm 3: System: Customer API
proctype CollectFromCustomer() {
    bit type;
    int customer_id, item_id, quantity, order_id;
    int i;

    do
    :: CO?type, customer_id, item_id, quantity -> {
        if
        :: (type == 0) -> {
            i = 0;
            do
            :: (i < DATABASE_SIZE) -> {
                if
                :: (actors[i].id == 0) -> {
                    CI[customer_id]!0, items[i].id, items[i].descr, items[i].how_many;
                    actors[i].id = customer_id;
                    actors[i].type = 0;
                }
                fi;
                i++;
            }
            :: else -> break;
            od;
        }
        :: (type == 1) -> {
            if
            :: (order_id < DATABASE_SIZE) -> {
                time++;
                orders[order_id].customer_id = customer_id;
                orders[order_id].item_id = item_id;
                orders[order_id].how_many = quantity;
                orders[order_id].date_placed = time;
                CI[customer_id]!1, order_id, 0, 0;
                order_id++;
            }
            fi;
        }
        fi;
    }
    od;
}

// Algorithm 4: System: Producer API
proctype ManageOrders() {
    int i, item_id, order_id, how_many, stock, needed_qty, producer_id;

    do
    :: true ->
        i = 0;
        do
        :: (i < DATABASE_SIZE) ->
            if
            :: (orders[i].date_processed == 0 || orders[i].date_ready == 0) ->
                item_id = orders[i].item_id;
                order_id = orders[i].id;
                how_many = orders[i].how_many;
                stock = items[item_id].how_many;

                // Segna l'ordine come processato
                if
                :: (orders[i].date_processed == 0) -> orders[i].date_processed = time;
                fi;

                if
                :: (stock >= how_many) ->
                    // Disponibilità sufficiente: l'ordine è pronto
                    orders[i].date_ready = time;
                    items[item_id].how_many = stock - how_many;
                :: else ->
                    // Disponibilità insufficiente: richiede produzione
                    needed_qty = how_many - stock;
                    producer_id = item_id % PRODUCER_NUMBER;
                    if
                    :: (needed_qty > 0) -> PI[producer_id]!1, item_id, needed_qty;
                    fi;
                fi;
            fi;
            i++;
        :: else -> skip;
        od;

        time++;
    od;
}


// Algorithm 5: System: Producer API auxiliary function
proctype SendProd() {
    int i, item_id, producer_id, qty_to_produce;

    do
    :: true ->
        i = 0;
        do
        :: (i < DATABASE_SIZE) ->
            if
            :: (!items[i].producing && items[i].how_many < items[i].how_many_min) ->
                item_id = items[i].id;
                qty_to_produce = items[i].how_many_min - items[i].how_many;
                producer_id = items[i].producer_id % PRODUCER_NUMBER;

                // Segna l'oggetto come in produzione e invia la richiesta al produttore
                items[i].producing = 1;
                PI[producer_id]!1, item_id, qty_to_produce;
            fi;
            i++;
        :: else -> break;
        od;
    od;
}

// Algorithm 6: System: Producer API function 2
proctype ManageMinStorage() {
    int i, item_id, needed_qty, producer_id;

    do
    :: true ->
        i = 0;
        do
        :: (i < DATABASE_SIZE) ->
            if
            :: (items[i].how_many < items[i].how_many_min) ->
                item_id = items[i].id;
                needed_qty = items[i].how_many_min - items[i].how_many;
                producer_id = items[i].producer_id % PRODUCER_NUMBER;

                // Richiede produzione per ripristinare la quantità minima
                PI[producer_id]!1, item_id, needed_qty;
            fi;
            i++;
        :: else -> break;
        od;
    od;
}

// Algorithm 7: System: Producer API function 3
proctype CollectFromProd() {
    bit type;
    int producer_id, item_id, quantity;

    do
    :: PO?type, producer_id, item_id, quantity ->
        if
        :: (type == 1) ->
            // Il produttore segnala il completamento della produzione
            items[item_id].producing = 0;
            items[item_id].how_many = items[item_id].how_many + quantity;
        fi;
    od;
}

// Algorithm 8: Environment: producer
proctype Producer(int pid_prod) {
    int item_id, quantity;

    // Inizializza il produttore
    PO!0, pid_prod, 0, 0;
    PI[pid_prod]?0, item_id, quantity;

    do
    :: PI[pid_prod]?1, item_id, quantity ->
        // Simula la produzione
        items[item_id].producing = 1;

        // Simulazione del tempo di produzione
        atomic {
            items[item_id].how_many = items[item_id].how_many + quantity;
            items[item_id].producing = 0;
        }

        // Segnala la produzione completata
        PO!1, pid_prod, item_id, quantity;
    od;
}

// Algorithm 9: System: shipper API function 1 when no work balance is needed
proctype SendOrders() {
    int i, order_id, item_id, quantity, shipper_id;

    do
    :: true ->
        i = 0;
        do
        :: (i < DATABASE_SIZE) ->
            if
            :: (orders[i].date_ready > 0 && orders[i].date_shipped == 0) ->
                order_id = orders[i].id;
                item_id = orders[i].item_id;
                quantity = orders[i].how_many;

                // Seleziona il corriere con meno carico
                shipper_id = i % SHIPPER_NUMBER;

                // Invia la richiesta di spedizione
                SI[shipper_id]!order_id, item_id, quantity;

                // Segna l'ordine come spedito
                orders[i].date_shipped = time;
            fi;
            i++;
        :: else -> break;
        od;

        time++;
    od;
}

// Algorithm 10: System: shipper API function 2
proctype CollectFromShip() {
    int shipper_id, order_id, temp_value;

    do
    :: SO?shipper_id, order_id, temp_value ->
        // Segna l'ordine come consegnato aggiornando la data di arrivo
        orders[order_id].date_arrived = time;
    od;
}


// Algorithm 11: Environment: shipper
proctype Shipper(int pid_ship) {
    int order_id, item_id, quantity, temp_value;

    // Inizializza il corriere
    SO!pid_ship, 0, 0;

    do
    :: SI[pid_ship]?order_id, item_id, quantity ->
        // Simula il tempo di consegna
        atomic {
            // Segnala la consegna completata con tutti i parametri necessari
            SO!pid_ship, order_id, item_id;
        }
    :: SO?pid_ship, order_id, temp_value ->
        // Ora riceve tutti i parametri richiesti dal canale SO
        skip;
    od;
}

// Algorithm 12: System: IntMonitor
proctype IntMonitor() {
    int i;

    do
    :: true ->
        i = 0;
        do
        :: (i < DATABASE_SIZE) ->
            if
            :: (orders[i].date_arrived - orders[i].date_placed > MAX_ELAPSED_TIME) ->
                anomalies[i] = 1; // Segnala un'anomalia per ordine in ritardo
            :: (time - orders[i].date_placed > MAX_ELAPSED_TIME) ->
                anomalies[i] = 1; // Segnala un'anomalia per ordine non ancora arrivato
            fi;
            i++;
        :: else -> break;
        od;

        time++;
    od;
}


init {
    atomic {
        // Avvio il processo per la generazione dell'ambiente (clienti, produttori, spedizionieri)
        run EnvGen(0); // Customers
        run EnvGen(1); // Producers
        run EnvGen(2); // Shippers

        // Avvio i processi di gestione del sistema
        run ManageOrders();
        run ManageMinStorage();
        run SendOrders();
        run CollectFromCustomer();
        run CollectFromProd();
        run CollectFromShip();
        run IntMonitor();

        // Creo le istanze dei clienti
        int i = 0;
        do
        :: (i < CUSTOMER_NUMBER) -> run Customer(i); i++;
        :: else -> break;
        od;

        // Creo le istanze dei produttori
        i = 0;
        do
        :: (i < PRODUCER_NUMBER) -> run Producer(i); i++;
        :: else -> break;
        od;

        // Creo le istanze dei corrieri
        i = 0;
        do
        :: (i < SHIPPER_NUMBER) -> run Shipper(i); i++;
        :: else -> break;
        od;
    }
}