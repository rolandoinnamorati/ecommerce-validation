# Progetto di Verifica e Validazione con Spin

## Struttura del Progetto
```
.
├── model_checking
    ├── ecommerce.pml     // Modello Promela
    └── property.ltl     // Proprietà LTL
├── unit_testing
    ├── customer
        ├── main.py // Unità di codice del cliente (da testare)
        ├── common_lib.py // Libreria utilizzata dall'unità
        └── test.py // Test per il cliente
    └── producer
└── README.md         // Documentazione del progetto
```

## Descrizione del Contesto
Il sistema oggetto di studio rappresenta un'organizzazione che vende oggetti tramite un sito web, coinvolgendo tre attori principali: clienti, produttori e consegnatori. Il sistema è costituito da sei processi concorrenti che interagiscono attraverso canali Redis per la gestione degli ordini, la produzione e la consegna degli oggetti. Il database PostgreSQL memorizza lo stato degli ordini e degli oggetti disponibili.

## Obiettivi del Progetto
1. **Model Checking con Spin**: Identificare eventuali problemi di comunicazione e deadlock nel sistema di e-commerce, verificando proprietà temporali con Spin e Promela.
2. **Unit Testing**: Selezionare due unità di codice e testarle con tecniche appropriate.
3. **Integration Testing**: Testare un insieme di sottounità per verificare l'interazione tra componenti.
4. **System Testing**: Verificare il funzionamento dell'intero sistema.
5. **Coverage Analysis**: Selezionare un'unità e verificare la coverage relativa a MC/DC e loop boundary, strumentando opportunamente il codice.