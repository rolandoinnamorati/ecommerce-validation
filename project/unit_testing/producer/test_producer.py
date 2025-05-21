import unittest
from unittest.mock import patch
import redis
import sys
import subprocess
import time
import random
import main

class TestProducer(unittest.TestCase):

    def generate_cases(self):
        test_cases = []
        #pochi item quantità medie
        test_cases.append(" ".join(f"{random.randint(1, 100)} {random.randint(10, 50)}" for _ in range(3)))
        #Più item quantità basse
        test_cases.append(" ".join(f"{random.randint(101, 200)} {random.randint(1, 10)}" for _ in range(5)))
        #id negativi
        test_cases.append(" ".join(f"{-random.randint(1, 50)} {random.randint(20, 80)}" for _ in range(4)))
        #singolo item
        test_cases.append(f"{random.randint(1, 10)} {random.randint(1, 100)}")
        return test_cases

    def test_main_function(self):
        print("\n--- Inizio test della funzione main ---")

        python_executable = sys.executable
        print(f"Usando interprete Python: {python_executable}")
        cmd = [
            python_executable,
            "/home/rolando/www/stv/project/unit_testing/producer/main.py",
            "-q", "work:queue:CO",
            "-Q", "work:queue:CI",
            "-t", "work:queue:TP",
            "-p", "3600",
            "-r", "42",
            "-i", "0",
            "localhost",
            "6379"
        ]

        for test in self.generate_cases():
            print(f"\n--- Eseguendo test con messaggio: '{test}' ---")

            R = redis.Redis(host="127.0.0.1", port=6379, decode_responses=True)
            R.delete("work:queue:CO")
            R.delete("work:queue:CI")
            R.delete("work:queue:TP")

            with open("output_producer.txt", "w") as outfile:
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

            R.lpush("work:queue:CI0", test)
            print(f"LPUSH (work:queue:CI) -> {test}")

            second_res = R.brpop("work:queue:CO", timeout=20)
            print(f"BRPOP (work:queue:CO) -> {second_res}")
            # if "prod" in second_res[1]:
            #     print("Produzione iniziata con successo")
            self.assertIn("prod", second_res[1], "Il messaggio non contiene 'prod'")

            #Invio la roba da produrre
            R.lpush("work:queue:CI0", test)
            print(f"LPUSH (work:queue:CI) -> {test}")
            tokens = test.split()
            for i in range(0, len(tokens), 2):
                res = R.brpop("work:queue:CO", timeout=10)
                print(f"BRPOP (work:queue:CO) -> {res}")
                self.assertEqual(res[1], tokens[i] + " " + tokens[i + 1], f"Errore nella produzione: {res[1]} != {tokens[i]} {tokens[i + 1]}")
                # if res[1] == tokens[i] + " " + tokens[i + 1]:
                #     print("Produzione avvenuta con successo")
                # else:
                #     self.fail("Produzione non avvenuta correttamente")

            #invio il comando per terminare il processo
            R.lpush("work:queue:TP0", "term")
            print("LPUSH (work:queue:TP) -> term")

            #aspetto che il processo figlio termini per evitare l'errore sul test
            time.sleep(5)

            #aspetto che il processo termini e mi risponda con term
            term_res = R.brpop("work:queue:CO", timeout=10)
            print(f"BRPOP (work:queue:CO) -> {term_res}")
            # if "term" in term_res[1]:
            #     print("Produzione terminata con successo")
            # else:
            #     self.fail("Il processo non ha terminato correttamente")
            self.assertIn("term", term_res[1], "Il processo non ha terminato correttamente")

            for _ in range(5):
                if process.poll() is not None:
                    break
                time.sleep(1)
            else:
                process.kill()
                self.fail("Il processo non è terminato correttamente")

        print("\n--- Fine test della funzione main ---")

if __name__ == '__main__':
    unittest.main()