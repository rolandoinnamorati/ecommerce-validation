#define DATABASE_SIZE 3
#define CHANNEL_SIZE 3
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
	bit date_placed;
	bit date_processed;
	bit date_ready;
	bit date_shipped;
	bit date_arrived;
}

Actor actors[DATABASE_SIZE];
Item items[DATABASE_SIZE];
Order orders[DATABASE_SIZE];

int anomalies[POSSIBLE_ANOMALIES];

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

// Algorithm 2: Environment: single customer issuing requests
proctype Customer(int pid_cust) {
 	int elem_id, descr, how_many;
	int selected, quantity;

    //Faccio la richiesta iniziale per ottere la lista degli elementi (i prodotti)
	CO!0, pid_cust, 0, 0;

	do
	    //Ricevo la risposta
    	:: CI[pid_cust]?0, elem_id, descr, how_many ->
    	        //Decisione non deterministica se ordinare o no
                if
                    :: selected = 0;  // Non ordina
                    :: selected = 1;  // Ordina
                fi;

        		if
                    :: (selected == 1 && how_many > 0) ->
                        quantity = 1;
                        do
                            :: (quantity < how_many) -> quantity++
                            :: break
                        od;

                        //Invia ordine
                        CO!1, pid_cust, elem_id, quantity;

                        //Attendo conferma ordine
                        CI[pid_cust]?1, elem_id, descr, how_many;
                    :: else -> skip  //Non ordina
                fi
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
                orders[order_id].customer_id = customer_id;
                orders[order_id].item_id = item_id;
                orders[order_id].how_many = quantity;
                orders[order_id].date_placed = 1;
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
                :: (orders[i].date_processed == 0) -> orders[i].date_processed = 1;
                fi;

                if
                :: (stock >= how_many) ->
                    // Disponibilità sufficiente: l'ordine è pronto
                    orders[i].date_ready = 1;
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
                orders[i].date_shipped = 1;
            fi;
            i++;
        :: else -> break;
        od;
    od;
}

// Algorithm 10: System: shipper API function 2
proctype CollectFromShip() {
    int shipper_id, order_id, temp_value;

    do
    :: SO?shipper_id, order_id, temp_value ->
        // Segna l'ordine come consegnato aggiornando la data di arrivo
        orders[order_id].date_arrived = 1;
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


init {
    atomic {
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