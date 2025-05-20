import unittest
from unittest.mock import patch
import redis
import sys
import subprocess
import time
import random
import main

class TestCustomer(unittest.TestCase):

    def compare_items(self, lpush_string, brpop_string):
        lpush_tokens = lpush_string.split()
        lpush = {}
        for i in range(1, len(lpush_tokens), 2):
            lpush[int(lpush_tokens[i])] = int(lpush_tokens[i+1])

        parts = brpop_string.split('|')
        brpop = {}
        for part in parts[1:]:
            tokens = part.split()
            if len(tokens) < 2:
                continue
            brpop[int(tokens[0])] = int(tokens[1])

        for item, qty in brpop.items():
            if item not in lpush:
                print(f"L'item {item} presente in BRPOP non è stato trovato in LPUSH.")
                return False
            if qty > lpush[item]:
                print(f"Errore per l'item {item}: quantità usata ({qty}) maggiore della quantità consentita ({lpush[item]}).")
                return False
        return True

    def generate_cases(self):
        return [
            "0 "
            + " ".join(
                f"{random.randint(1, 20)} {random.randint(1, 100)}"
                for _ in range(random.randint(2, 5))
            ),
            "0 "
            + " ".join(
                f"{random.choice([0, random.randint(1, 20)])} {random.randint(1, 100)}"
                for _ in range(random.randint(2, 5))
            ),
            "0 "
            + " ".join(
                f"{-random.randint(1, 20)} {random.choice([random.randint(1, 50), random.randint(1, 50)])}"
                for _ in range(random.randint(2, 5))
            ),
        ]

    def generate_various_item_lists(self):
        """
        Genera una serie di liste di elementi e intervalli di selezione
        per testare la funzione di estrazione di sottoinsiemi.
        Ogni tupla è (lista_elementi_disponibili, lunghezza_minima, lunghezza_massima).
        """
        scenari_di_test = [
            ([], 0, 0),                                           # Lista vuota, range 0
            ([random.randint(1, 100)], 1, 1),                     # Lista singola, range 1
            ([random.randint(1, 100) for _ in range(random.randint(3, 6))], 2, 4), # Lista media, range valido
            ([random.choice([0, random.randint(1, 100)]) for _ in range(random.randint(3, 6))], 2, 4), # Lista con 0, range valido
            ([random.choice([-random.randint(1, 100), random.randint(1, 100)]) for _ in range(random.randint(3, 6))], 2, 4), # Lista con negativi, range valido
            ([random.randint(1, 100) for _ in range(2)], 3, 4),   # Lista più corta del minimo richiesto
            ([random.randint(1, 100) for _ in range(4)], 3, 2),   # Minimo > Massimo (dovrebbe causare errore)
            ([random.randint(1, 100) for _ in range(5)], 2, 3),   # Lista più lunga del massimo, ma range valido
            ([random.randint(1, 100) for _ in range(5)], 2, 6),   # Lista con lunghezza entro il range max
            ([random.randint(1, 100) for _ in range(4)], 0, 0)    # Lista non vuota, range 0
        ]
        return scenari_di_test

    def test_main_function(self):
        print("\n--- Inizio test della funzione main ---")


        python_executable = sys.executable
        print(f"Usando interprete Python: {python_executable}")
        cmd = [
            python_executable,
            "/home/rolando/www/stv/project/unit_testing/customer/main.py",
            "-r", "42",
            "-q", "work:queue:CO",
            "-Q", "work:queue:CI",
            "-i", "0", #fun_name_glob = "customer_env_0"
            "-m", "3",
            "-M", "6",
            "localhost",
            "6379"
        ]

        for category_var in self.generate_cases():
            print(f"\n--- Eseguendo test con messaggio: '{category_var}' ---")

            # Collegati a Redis
            R = redis.Redis(host="127.0.0.1", port=6379, decode_responses=True)
            R.delete("work:queue:CO")
            R.delete("work:queue:CI0")

            with open("output_customer.txt", "w") as outfile:
                process = subprocess.Popen(
                    cmd,
                    stdout=outfile,
                    stderr=outfile,
                    text=True
                )
                print(f"PID del processo: {process.pid}")

            time.sleep(5)

            first_res = R.brpop("work:queue:CO", timeout=0)
            print(f"BRPOP (work:queue:CO) -> {first_res}")

            R.lpush("work:queue:CI0", category_var)
            print(f"LPUSH (work:queue:CI0) -> {category_var}")

            second_res = R.brpop("work:queue:CO", timeout=20)
            print(f"BRPOP (work:queue:CO) -> {second_res[1]}")
            if second_res != None and self.compare_items(category_var, second_res[1]):
                print("TEST OK, numero di items corretto")
            else:
                print("TEST KO, numero di items troppo alto o errato")

            R.lpush("work:queue:CI0", "OK")
            print("LPUSH (work:queue:CI0, 'OK')")
            print("--- Fine operazioni su Redis ---\n")

            try:
                process.communicate(timeout=5)
            except subprocess.TimeoutExpired:
                process.kill()
                self.fail("Il processo main.py ha superato il timeout di 5 secondi")

            self.assertEqual(process.returncode, 0, "Il processo main.py ha restituito un codice di errore")

            with open("output_customer.txt", "r") as infile:
                output = infile.read()

            self.assertIn("Sleeping", output, "Il messaggio Sleeping non è presente nell'output")

        print("\n--- Fine test della funzione main ---")

    def test_item_subset_selection_logic(self):
        print("\n--- Inizio test della logica di selezione del sottoinsieme di elementi ---")

        all_test_scenarios = self.generate_various_item_lists()

        for scenario_idx, (available_items, min_count, max_count) in enumerate(all_test_scenarios):
            test_id = f"Scenario {scenario_idx}: Items={available_items}, Min={min_count}, Max={max_count}"
            print(f"\n--- Esecuzione {test_id} ---")

            with self.subTest(test_id):
                try:
                    selected_subset = main.pick_subset(available_items, min_count, max_count)
                    print(f"Risultato della selezione: {selected_subset}")

                    # Asserzione 1: La lunghezza del sottoinsieme deve essere valida
                    # Deve essere tra min_count e max_count, oppure uguale alla lunghezza di 'available_items'
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
                    if min_count > len(available_items):
                        self.assertCountEqual(selected_subset, available_items,
                                              "Quando min_count > len(items), tutti gli items disponibili dovrebbero essere selezionati.")
                        print("   ✓ Copertura totale: selezionati tutti gli elementi disponibili come previsto.")

                    # Asserzione 5: Se min_count è maggiore di max_count, ci aspettiamo un ValueError.
                    # Se non viene sollevato e si arriva qui, il test fallisce.
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

if __name__ == '__main__':
    unittest.main()
