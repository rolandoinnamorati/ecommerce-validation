import unittest
from unittest.mock import patch, MagicMock
from main import parse_args, common_lib, pick_subset

class TestRedisIntegration(unittest.TestCase):
    @patch('main.common_lib.redis_command')
    def test_full_redis_flow(self, mock_redis_command):
        with patch('sys.argv', ["main.py", "localhost", "6379"]):
            args = parse_args()

        #Simulo la connessione Redis con un mock
        mock_redis = MagicMock()

        # Simulo `LPUSH`
        queue_co_command = "LPUSH " + args.queue_co + " init " + str(args.index_cust)
        mock_redis_command.return_value = None  # LPUSH non ha un risultato utile
        common_lib.redis_command(mock_redis, queue_co_command)
        mock_redis_command.assert_called_with(mock_redis, queue_co_command)

        # Simulo `BRPOP` con una risposta valida
        expected_brpop_command = "BRPOP " + args.queue_ci_base + str(args.index_cust) + " 0"
        mock_redis_command.return_value = ["queue_name", "12 101 3 102 7 103 2"]
        resp = common_lib.redis_command(mock_redis, expected_brpop_command)

        #Parsing risposta BRPOP
        res = resp[1].split()
        index_cust_db = res[0]
        I = {int(res[i]): int(res[i + 1]) for i in range(1, len(res), 2)}

        #Validao la risposta
        self.assertEqual(index_cust_db, "12")
        self.assertEqual(I, {101: 3, 102: 7, 103: 2})

class TestPickSubset(unittest.TestCase):

    def test_pick_subset_within_range(self):
        #Imposta min_items e max_items
        min_items = 5
        max_items = 10
        I = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

        result = pick_subset(I, min_items, max_items)

        #la lunghezza del risultato deve essere tra min_items e max_items
        self.assertGreaterEqual(len(result), min_items)
        self.assertLessEqual(len(result), max_items)

        # Nessun duplicato nel risultato
        self.assertEqual(len(result), len(set(result)))

class TestSleepWrap(unittest.TestCase):

    @patch('main.common_lib.sleep_wrap')
    def test_sleep_wrap_called(self, mock_sleep_wrap):
        rc = None #Ignoro il valore dirc
        common_lib.sleep_wrap(rc, cause="think_time")

        mock_sleep_wrap.assert_called_once_with(rc, cause="think_time")

class TestTerminateTime(unittest.TestCase):

    @patch('main.common_lib.terminate_time')
    def test_terminate_time_called(self, mock_terminate_time):
        rc = None
        common_lib.terminate_time(rc)

        mock_terminate_time.assert_called_once_with(rc)

class TestRedisCommands(unittest.TestCase):

    @patch('main.common_lib.redis_command')
    def test_redis_commands(self, mock_redis_command):
        #Risimulo l'interazione con redis
        rc = None
        queue_co = "queue_co"
        mock_redis_command.return_value = "OK"

        common_lib.redis_command(rc, "LPUSH " + queue_co + " message")
        mock_redis_command.assert_called_once_with(rc, "LPUSH " + queue_co + " message")

        queue_ci_base = "queue_ci_base"
        mock_redis_command.return_value = ["", "123 456"]

        response = common_lib.redis_command(rc, "BRPOP " + queue_ci_base + " 0")
        mock_redis_command.assert_called_with(rc, "BRPOP " + queue_ci_base + " 0")

if __name__ == '__main__':
    unittest.main()
