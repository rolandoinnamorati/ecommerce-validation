import unittest
from unittest.mock import patch
import redis
import sys
import subprocess
import time
import random
# Assicurati che main (producer) sia importabile. Potrebbe essere necessario modificare il PATH
# o copiare main.py nella stessa directory del test.
import main as producer_main # Importa il main del producer come producer_main
import common_lib # Se common_lib è nella stessa directory del test

class TestProducer(unittest.TestCase):

    def compare_producer_output_items(self, lpush_string, brpop_string):
        """
        Compara l'input inviato al producer (la lista di item disponibili)
        con l'output ricevuto dal producer (gli item che "produce").
        Asserisce che gli item prodotti siano validi e in quantità accettabile.
        """
        # Parsing dell'input LPUSH (la "availability" passata al producer)
        # Formato: "item1 item_qty1 item2 item_qty2 ..."
        lpush_tokens = lpush_string.split()
        lpush_items = {}
        # Il tuo producer/main.py invia solo ID item al random.sample
        # Non sembra che usi le quantità dall'input della coda PI
        # Quindi, qui ci concentriamo solo sugli ID degli item forniti in input.
        # Ad esempio, se l'input è "1 10 2 20", il produttore riceve [1, 2] come I.keys().
        # Per questo test, ci interessa che i "prodotti" siano nella lista iniziale degli ID.
        for i in range(0, len(lpush_tokens), 2): # Modificato per parsare l'input del producer
            try:
                lpush_items[int(lpush_tokens[i])] = int(lpush_tokens[i+1])
            except (ValueError, IndexError):
                print(f"Errore di parsing in lpush_string: {lpush_string}. Token: {lpush_tokens[i]}, {lpush_tokens[i+1]}")
                return False

        # Parsing dell'output BRPOP dal producer (es. "prod 0 1 50")
        # Formato: "num_items|item_id qty item_id qty..."
        # Il tuo main.py genera "prod 0 <item_id> <m>"
        # O "num|item_id qty <index_cust_db> <index_cust>|..." per il customer
        # Il producer invia "LPUSH " + args.queue_po + " " + i + " " + str(m)
        # Quindi l'output sarà "item_id m"
        brpop_tokens = brpop_string.split()
        if len(brpop_tokens) < 2:
            print(f"Formato BRPOP non valido: {brpop_string}")
            return False

        # Il producer invia LPUSH <queue_po> <item_id> <m>
        # Quindi l'output letto dal test sarà solo "item_id m"
        try:
            produced_item_id = int(brpop_tokens[0])
            produced_quantity = int(brpop_tokens[1])
        except (ValueError, IndexError):
            print(f"Errore di parsing in brpop_string: {brpop_string}. Token: {brpop_tokens[0]}, {brpop_tokens[1]}")
            return False

        # Verifica 1: L'ID dell'item prodotto deve essere uno degli item forniti in input
        if produced_item_id not in lpush_items:
            print(f"Errore: L'item {produced_item_id} prodotto non era nella lista degli item forniti in input ({lpush_items.keys()}).")
            return False

        # Verifica 2: La quantità prodotta deve essere positiva (il codice usa randint(1, I[j]))
        if produced_quantity <= 0:
            print(f"Errore: Quantità prodotta ({produced_quantity}) deve essere maggiore di zero.")
            return False

        # Potresti aggiungere altre verifiche sulla quantità se il producer ha vincoli
        # sul max che può produrre basandosi sulla disponibilità iniziale o altri fattori.
        # Per ora, controlliamo solo che la quantità non superi una logica ragionevole
        # ad esempio, non superi un valore massimo arbitrario se non c'è un limite superiore definito.
        # Dato che `main.py` usa `random.randint(1, I[j])` per `m` nel producer,
        # la `I[j]` dal customer, che non è rilevante qui, non è un limite.
        # Il producer produce solo un item alla volta.
        # Per la logica di `producer/main.py`: `send += str(j) + " " + str(random.randint(1, I[j]))`
        # dove `I` è `random.sample(resp_ar, random.randint(1, len(resp_ar) - 1))`
        # Qui `I[j]` non è la quantità in input, ma un valore a caso dalla `resp_ar` originale.
        # È una parte un po' confusa della logica del producer.
        # Per ora, ci accontentiamo che l'item sia valido e la quantità > 0.

        return True


    def generate_producer_test_cases(self):
        """
        Genera casi di test per il producer.
        Ogni caso è una lista di item (ID e quantità) che il producer dovrebbe ricevere.
        """
        test_cases = []
        # Caso 1: Pochi item con quantità medie
        test_cases.append(" ".join(f"{random.randint(1, 100)} {random.randint(10, 50)}" for _ in range(3)))
        # Caso 2: Più item, alcune quantità basse
        test_cases.append(" ".join(f"{random.randint(101, 200)} {random.randint(1, 10)}" for _ in range(5)))
        # Caso 3: Item con ID negativi (il tuo `main.py` gestisce `int(res[i])`)
        test_cases.append(" ".join(f"{-random.randint(1, 50)} {random.randint(20, 80)}" for _ in range(4)))
        # Caso 4: Un singolo item
        test_cases.append(f"{random.randint(1, 10)} {random.randint(1, 100)}")
        return test_cases

    def test_producer_main_function(self):
        """
        Test end-to-end della funzione main del producer.
        Simula la comunicazione Redis per verificare il flusso di lavoro.
        """
        print("\n--- Inizio test della funzione main del Producer ---")

        python_executable = sys.executable
        print(f"Usando interprete Python: {python_executable}")
        producer_cmd = [
            python_executable,
            "/home/rolando/www/stv/project/unit_testing/producer/main.py",
            "-r", "42",
            "-q", "work:queue:PO",       # Queue for Producer Output
            "-Q", "work:queue:PI",       # Queue for Producer Input (base)
            "-t", "work:queue:TP",       # Queue for Termination (base)
            "-i", "0",                   # index_prod (per fun_name_glob = "producer_env_0")
            "localhost",
            "6379"
        ]

        for input_items_str in self.generate_producer_test_cases():
            print(f"\n--- Esecuzione test Producer con input: '{input_items_str}' ---")

            redis_conn = redis.Redis(host="127.0.0.1", port=6379, decode_responses=True)
            print("Connessione a Redis stabilita")

            # Pulizia aggressiva delle code Redis per ogni caso di test
            # Adatta i nomi delle code in base ai parametri del producer_cmd
            redis_conn.delete("work:queue:PO")
            redis_conn.delete("work:queue:PI0") # PI + index_prod
            redis_conn.delete("work:queue:TP0") # TP + index_prod
            redis_conn.delete("work:queue:INIT_BARR_SEND")
            redis_conn.delete("work:queue:producer_env_0_0") # Sincronizzazione interna del producer
            redis_conn.delete("work:queue:producer_env_0_1") # Sincronizzazione interna del producer


            with open("producer_output.txt", "w") as outfile: # Output specifico per il producer
                process = subprocess.Popen(
                    producer_cmd,
                    stdout=outfile,
                    stderr=outfile,
                    text=True
                )
                print(f"PID del processo Producer: {process.pid}")

            # Dare tempo al producer per avviarsi e mettersi in ascolto sul PRIMO BRPOP
            time.sleep(0.5)

            # 1. Sblocco del PRIMO BRPOP del producer (su `work:queue:producer_env_0_1`)
            initial_sync_msg = "0 0" # Formato per `starting_int_glob` e `curr_elapsed_glob`
            redis_conn.lpush("work:queue:producer_env_0_1", initial_sync_msg)
            print(f"LPUSH (work:queue:producer_env_0_1) -> '{initial_sync_msg}' per sbloccare il producer.")

            # 2. Il producer dovrebbe ora inviare il suo messaggio "init" su work:queue:PO
            print("Attesa del messaggio 'init' da Producer su work:queue:PO...")
            first_prod_res = redis_conn.brpop("work:queue:PO", timeout=10)
            if first_prod_res:
                print(f"BRPOP (work:queue:PO) -> {first_prod_res}")
                self.assertEqual(first_prod_res[1], "init 0", "Il producer non ha inviato il messaggio 'init' corretto.")
            else:
                self.fail("Il producer non ha inviato il messaggio 'init' su work:queue:PO in tempo.")

            # 3. Inviamo l'input di "Availability" al producer su work:queue:PI0
            print(f"LPUSH (work:queue:PI0) -> {input_items_str}")
            redis_conn.lpush("work:queue:PI0", input_items_str)

            # 4. Il producer dovrebbe elaborare e spingere gli item prodotti su work:queue:PO
            # Il producer invia un item per volta.
            # Questo loop gestisce il fatto che il producer può dormire (sleep_wrap)
            # prima di inviare l'output. Ha un ciclo infinito.
            # Dobbiamo simulare che il producer produca N item e poi lo termini.
            # Quanti item produce? random.sample(resp_ar, random.randint(1, len(resp_ar) - 1))
            # len(resp_ar) è il numero di token nell'input_items_str. Se input_items_str è "1 10 2 20", len è 4.
            # pick_subset usa len(I) come numero massimo.
            # Il producer chiama `common_lib.sleep_wrap(rc, cause="prod_time")` e poi `LPUSH`
            # Quindi dobbiamo fare un `BRPOP` per ogni item che ci aspettiamo.
            # Per semplicità, in questo test, proviamo a leggere un singolo item prodotto.
            # Il producer poi dorme (main_sleep) e attende un altro input.
            # Per terminare, deve ricevere un messaggio sulla coda TP.

            print("Attesa del messaggio di produzione da Producer su work:queue:PO...")
            produced_item_msg = redis_conn.brpop("work:queue:PO", timeout=20) # Timeout più lungo
            if produced_item_msg:
                print(f"BRPOP (work:queue:PO) -> {produced_item_msg[1]}")
                # Ora confrontiamo l'output del producer con l'input iniziale
                is_valid_production = self.compare_producer_output_items(input_items_str, produced_item_msg[1])
                self.assertTrue(is_valid_production, f"Produzione non valida per input '{input_items_str}'. Output: {produced_item_msg[1]}")
                print("   ✓ Produzione verificata: Item valido e quantità > 0.")
            else:
                self.fail("Il producer non ha inviato un messaggio di produzione su work:queue:PO in tempo.")

            # 5. Terminare il producer inviando "TERM" sulla sua coda di terminazione (TP0)
            print("Invio del messaggio 'TERM' al Producer su work:queue:TP0...")
            redis_conn.lpush("work:queue:TP0", "TERM")

            # 6. Il producer dovrebbe poi completare la sua logica di terminazione (che include una barriera)
            # common_lib.terminate_time(rc) -> ba_redis_command(rc, also_barrier_glob, "LPUSH %s %s" %(base_channel + "_0", "TERM"))
            #                                  ba_redis_command(rc, also_barrier_glob, "BRPOP %s %d" %(base_channel + "_1", 0))
            print("Attesa della richiesta di terminazione da Producer su work:queue:producer_env_0_0...")
            producer_term_req = redis_conn.brpop("work:queue:producer_env_0_0", timeout=5)
            if producer_term_req and producer_term_req[1] == "TERM":
                print(f"Ricevuto 'TERM' dal producer. Rispondo su work:queue:producer_env_0_1 per ACK.")
                redis_conn.lpush("work:queue:producer_env_0_1", "ACK_TERM")
            else:
                self.fail(f"Il producer non ha inviato 'TERM' come atteso o timeout scaduto. Messaggio: {producer_term_req}")

            # 7. Aspetta che il processo subprocess termini
            try:
                process.communicate(timeout=5)
            except subprocess.TimeoutExpired:
                process.kill()
                self.fail("Il processo producer/main.py ha superato il timeout di 5 secondi per la terminazione.")

            self.assertEqual(process.returncode, 0, "Il processo producer/main.py ha restituito un codice di errore non zero.")

            with open("producer_output.txt", "r") as infile:
                output = infile.read()
            self.assertIn("Sleeping", output, "Il messaggio 'Sleeping' non è presente nell'output del producer.")
            self.assertIn("exited normally", output, "Il messaggio di uscita normale non è presente nell'output del producer.")

        print("\n--- Fine test della funzione main del Producer ---")


    # Nuovi test per la funzione parse_args del producer
    def test_producer_parse_args_valid_case(self):
        """Verifica il parsing corretto degli argomenti per il producer."""
        args = [
            'producer_main.py',
            '-r', '123',
            '-q', 'prod_out_q',
            '-Q', 'prod_in_q_base',
            '-t', 'term_q_base',
            '-i', '5',
            'another_host',
            '6380'
        ]
        with patch('sys.argv', args):
            parsed_args = producer_main.parse_args()
        self.assertEqual(parsed_args.rand_seed, 123)
        self.assertEqual(parsed_args.queue_po, 'prod_out_q')
        self.assertEqual(parsed_args.queue_pi_base, 'prod_in_q_base')
        self.assertEqual(parsed_args.queue_t_base, 'term_q_base')
        self.assertEqual(parsed_args.index_prod, 5)
        self.assertEqual(parsed_args.redishost, 'another_host')
        self.assertEqual(parsed_args.redisport, '6380')

    def test_producer_parse_args_invalid_queues(self):
        """Verifica che la parse_args del producer gestisca code vuote."""
        args = [
            'producer_main.py',
            '-q', '', # Coda PO vuota
            '-Q', 'valid_q',
            '-t', 'valid_t_q',
            '-i', '0',
            'localhost', '6379'
        ]
        with patch('sys.argv', args):
            with self.assertRaises(SystemExit) as cm:
                producer_main.parse_args()
            self.assertEqual(cm.exception.code, 2) # SystemExit con codice 2 per errore

        args[3] = 'valid_q' # Reimposta queue_po
        args[5] = ''        # Coda PI_base vuota
        with patch('sys.argv', args):
            with self.assertRaises(SystemExit) as cm:
                producer_main.parse_args()
            self.assertEqual(cm.exception.code, 2)

        args[5] = 'valid_q' # Reimposta queue_pi_base
        args[7] = ''        # Coda T_base vuota
        with patch('sys.argv', args):
            with self.assertRaises(SystemExit) as cm:
                producer_main.parse_args()
            self.assertEqual(cm.exception.code, 2)

    def test_producer_parse_args_negative_index_prod(self):
        """Verifica che index_prod negativo causi un errore."""
        args = [
            'producer_main.py',
            '-i', '-1',
            '-q', 'valid_q',
            '-Q', 'valid_q',
            '-t', 'valid_q',
            'localhost', '6379'
        ]
        with patch('sys.argv', args):
            with self.assertRaises(SystemExit) as cm:
                producer_main.parse_args()
            self.assertEqual(cm.exception.code, 2)

    # Nota: il producer main.py ha solo prod_time, non min_items/max_items o index_cust
    # Quindi non ci sono test per quei parametri specifici del consumer.

    # Funzione pick_subset dal producer main.py (se vuoi testarla)
    # def pick_subset(I, minl, maxl):
    #     hm = random.randint(min(len(I), minl), min(len(I), maxl))
    #     ret = []
    #     for i in range(hm):
    #         while True:
    #             pick = random.choice(I)
    #             if pick not in ret:
    #                 ret += [pick]
    #                 break
    #     return ret

    # Se vuoi testare pick_subset del producer, potresti aggiungere un metodo simile a quello del customer:
    def generate_producer_subsets_cases(self):
        # Questi sono gli stessi scenari che hai già testato per pick_subset
        # Potresti riutilizzare generate_various_item_lists se la firma è la stessa
        return [
            ([], 0, 0),
            ([random.randint(1, 100)], 1, 1),
            ([random.randint(1, 100) for _ in range(random.randint(3, 6))], 2, 4),
            ([random.choice([0, random.randint(1, 100)]) for _ in range(random.randint(3, 6))], 2, 4),
            ([random.choice([-random.randint(1, 100), random.randint(1, 100)]) for _ in range(random.randint(3, 6))], 2, 4),
            ([random.randint(1, 100) for _ in range(2)], 3, 4),
            ([random.randint(1, 100) for _ in range(4)], 3, 2), # min > max: expected ValueError
            ([random.randint(1, 100) for _ in range(5)], 2, 3),
            ([random.randint(1, 100) for _ in range(5)], 2, 6),
            ([random.randint(1, 100) for _ in range(4)], 0, 0)
        ]

    def test_producer_pick_subset_logic(self):
        """
        Verifica la correttezza della funzione pick_subset del producer.
        """
        print("\n--- Inizio test della logica di selezione del sottoinsieme per il Producer ---")
        all_test_scenarios = self.generate_producer_subsets_cases()

        for scenario_idx, (available_items, min_count, max_count) in enumerate(all_test_scenarios):
            test_id = f"Scenario {scenario_idx}: Items={available_items}, Min={min_count}, Max={max_count}"
            print(f"\n--- Esecuzione {test_id} ---")

            with self.subTest(test_id):
                try:
                    selected_subset = producer_main.pick_subset(available_items, min_count, max_count)
                    print(f"Risultato della selezione: {selected_subset}")

                    # Asserzione 1: La lunghezza del sottoinsieme deve essere valida
                    # NOTA: La logica `min(len(I), minl), min(len(I), maxl)` in producer_main.pick_subset
                    # significa che `hm` sarà sempre <= `len(I)`.
                    # Quindi, la condizione `len(subset) == len(available_items)` per `min_count > len(available_items)`
                    # o `max_count < len(available_items)` potrebbe non essere necessaria
                    # se la funzione non è pensata per restituire tutti gli item in quel caso.
                    # Rivedi la logica di `pick_subset` se necessario.
                    # Per ora, la lasciamo come era per il customer.
                    expected_length_condition = (
                            (min_count <= len(selected_subset) <= max_count) or
                            (len(selected_subset) == len(available_items) and min_count > len(available_items)) or
                            (len(selected_subset) == len(available_items) and max_count < len(available_items) and len(selected_subset) >= min_count)
                    )
                    self.assertTrue(expected_length_condition,
                                    f"Lunghezza sottoinsieme ({len(selected_subset)}) non conforme al range [{min_count}, {max_count}] o disponibilità ({len(available_items)}).")
                    print(f"   ✓ Lunghezza verificata: {len(selected_subset)} elementi (attesi tra {min_count} e {max_count} o pari a {len(available_items)}).")

                    # Asserzione 2: Tutti gli elementi selezionati devono provenire dalla lista iniziale
                    self.assertTrue(set(selected_subset).issubset(set(available_items)),
                                    "Gli elementi selezionati non sono un sottoinsieme valido degli elementi disponibili.")
                    print("   ✓ Validità sottoinsieme: tutti gli elementi sono presenti nella lista iniziale.")

                    # Asserzione 3: Nessun elemento duplicato nel sottoinsieme risultante
                    self.assertEqual(len(set(selected_subset)), len(selected_subset),
                                     "Il sottoinsieme contiene elementi duplicati.")
                    print("   ✓ Unicità elementi: nessun elemento ripetuto nel sottoinsieme.")

                    # Asserzione 4: Se il minimo richiesto è maggiore della lista disponibile,
                    # il sottoinsieme dovrebbe contenere tutti gli elementi disponibili.
                    # Questa assertione è per il caso in cui `pick_subset` sia progettata
                    # per restituire tutto se la richiesta minima è maggiore della disponibilità.
                    if min_count > len(available_items):
                        self.assertCountEqual(selected_subset, available_items,
                                              "Quando min_count > len(items), tutti gli items disponibili dovrebbero essere selezionati.")
                        print("   ✓ Copertura totale: selezionati tutti gli elementi disponibili come previsto.")

                    # Asserzione 5: Se min_count è maggiore di max_count, ci aspettiamo un ValueError.
                    if min_count > max_count:
                        self.fail(f"Errore: si attendeva un ValueError per min_count={min_count} > max_count={max_count}, ma la funzione è stata eseguita con successo: {selected_subset}")

                    # Asserzione 6: Se sia min_count che max_count sono zero, il sottoinsieme deve essere vuoto.
                    if min_count == 0 and max_count == 0:
                        self.assertEqual(selected_subset, [],
                                         "Il sottoinsieme non è vuoto con range [0, 0].")
                        print("   ✓ Sottoinsieme vuoto: il risultato è vuoto per range [0, 0].")

                except ValueError as e:
                    # Gestiamo l'errore atteso per il caso min_count > max_count
                    if min_count > max_count:
                        print(f"   ✓ Errore atteso catturato (min > max): {e}")
                    else:
                        self.fail(f"Errore inaspettato di tipo ValueError per min_count={min_count}, max_count={max_count}: {e}")

        print("\n--- Fine test della logica di selezione del sottoinsieme per il Producer ---")


if __name__ == '__main__':
    unittest.main()