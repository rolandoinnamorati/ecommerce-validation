# Progetto di Verifica e Validazione con Spin

## Struttura del Progetto
```
.
├── ecommerce.pml     // Modello Promela
├── proprietà.ltl     // Proprietà LTL (opzionale)
├── pan.c             // Codice C generato da Spin
├── pan               // Eseguibile
├── trailfile         // Trace file in caso di errore
└── README.md         // Documentazione del progetto
```

## Descrizione del Contesto
Il sistema oggetto di studio rappresenta un'organizzazione che vende oggetti tramite un sito web, coinvolgendo tre attori principali: clienti, produttori e consegnatori. Il sistema è costituito da sei processi concorrenti che interagiscono attraverso canali Redis per la gestione degli ordini, la produzione e la consegna degli oggetti. Il database PostgreSQL memorizza lo stato degli ordini e degli oggetti disponibili.

## Modellazione con Spin e Promela
### Definizione dei Canali di Comunicazione
In Promela, i canali simulano i messaggi su Redis:
```c
chan CO = [10] of { int }; // Canale per le richieste clienti
chan SIs = [10] of { int }; // Canale per i consegnatori
```

### Modellazione dei Processi
Processo cliente:
```c
active proctype Customer() {  
    int item_id;  
    do  
    :: item_id = 1; CO!item_id;  
    :: item_id = 2; CO!item_id;  
    :: item_id = 3; CO!item_id;  
    od  
}
```

Processo gestione ordini:
```c
active proctype OrderManager() {  
    int item_id;  
    do  
    :: CO?item_id ->  
       if  
       :: db[item_id-1] > 0 -> db[item_id-1]--; ORD!item_id;  
       :: else -> printf("Prodotto esaurito: %d\n", item_id);  
       fi;  
    od  
}
```

Processo consegnatore:
```c
active proctype Shipper() {  
    int order_id;  
    do  
    :: ORD?order_id ->  
       printf("Consegna dell'oggetto %d\n", order_id);  
       SIs!order_id;  
    od  
}
```

Monitor per rilevare errori:
```c
active proctype Monitor() {  
    do  
    :: SIs?_;  
    :: skip;  
    od  
}
```

### Specifica della Proprietà LTL
```c
ltl no_deadlock { []<> SIs } // Sempre prima o poi avviene una consegna
```

## Istruzioni per l'Esecuzione
1. **Simulazione**:
```sh
spin ecommerce.pml  
```
2. **Verifica**:
```sh
spin -run ecommerce.pml  
```
3. **Generazione del verificatore**:
```sh
spin -a ecommerce.pml  
gcc -o pan pan.c  
./pan  
```

## Obiettivi del Progetto
1. **Model Checking con Spin**: Identificare eventuali problemi di comunicazione e deadlock nel sistema di e-commerce, verificando proprietà temporali con Spin e Promela.
2. **Unit Testing**: Selezionare sei unità di codice e testarle con tecniche appropriate.
3. **Integration Testing**: Testare tre insiemi di sottounità per verificare l'interazione tra componenti.
4. **System Testing**: Verificare il funzionamento dell'intero sistema.
5. **Coverage Analysis**: Selezionare un'unità e verificare la coverage relativa a MC/DC e loop boundary, strumentando opportunamente il codice.