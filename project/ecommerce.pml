// Canali di comunicazione
chan CO = [10] of { int };   // Richieste clienti
chan ORD = [10] of { int };  // Ordini da processare
chan SIs = [10] of { int };  // Consegne

// Stato del database simulato
int db[3] = 3, 5, 2; // Disponibilità degli oggetti (id 1, 2, 3)

// Processo Cliente
active proctype Customer() {  
    int item_id;  
    do  
    :: item_id = 1; CO!item_id;  
    :: item_id = 2; CO!item_id;  
    :: item_id = 3; CO!item_id;  
    od  
}

// Processo Gestore Ordini
active proctype OrderManager() {  
    int item_id;  
    do  
    :: CO?item_id ->  
       if  
       :: db[item_id-1] > 0 -> db[item_id-1]--; ORD!item_id;  
       :: else -> printf(\"Prodotto esaurito: %d\\n\", item_id);  
       fi;  
    od  
}

// Processo Consegna
active proctype Shipper() {  
    int order_id;  
    do  
    :: ORD?order_id ->  
       printf(\"Consegna dell'oggetto %d\\n\", order_id);  
       SIs!order_id;  
    od  
}

// Monitor per rilevare errori
active proctype Monitor() {  
    do  
    :: SIs?_;  
    :: skip;  
    od  
}

#include property.ltl