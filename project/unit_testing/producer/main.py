import common_lib
import sys
import argparse
import datetime
import os
import json
import redis
import more_itertools
import random

def main():
    args = parse_args()
    common_lib.init_rand(args.rand_seed)
    rc = redis.Redis(host=args.redishost, port=args.redisport, decode_responses=True)
    fun_name = "producer_env_" + str(args.index_prod)
    common_lib.init_time(rc, False, fun_name)
    common_lib.redis_command(rc, "LPUSH " + args.queue_po + " init " + str(args.index_prod))
    resp = common_lib.redis_command(rc, "BRPOP " + args.queue_pi_base + str(args.index_prod) + " 0")[1]
    resp_ar = resp.split()
    # print("DBG" + str(resp_ar))
    I = random.sample(resp_ar, random.randint(1, len(resp_ar) - 1))
    tbs = str(I).replace("[", "").replace("]", "").replace(",", "").replace("'", "")
    common_lib.redis_command(rc, "LPUSH " + args.queue_po + " prod " + str(args.index_prod) + " " + tbs)
    while True:
        X = common_lib.redis_command(rc, "RPOP " + args.queue_t_base + str(args.index_prod))
        if X != None:
            common_lib.redis_command(rc, "LPUSH " + args.queue_po + " term " + str(args.index_prod))
            common_lib.terminate_time(rc)
            print(common_lib.fun_name_glob + " exited because asked")
            sys.stdout.flush()
            sys.exit(0)
        X = common_lib.redis_command(rc, "RPOP " + args.queue_pi_base + str(args.index_prod))
        if X != None:
            Xar = X.split()
            for l in range(0, len(Xar), 2):
                i = Xar[l]
                m = int(Xar[l + 1])
                print("Producing " + str(m) + " items")
                sys.stdout.flush()
                # for j in range(m): #too much
                #     common_lib.sleep_wrap(rc, cause="prod_time")
                common_lib.sleep_wrap(rc, cause="prod_time")
                common_lib.redis_command(rc, "LPUSH " + args.queue_po + " " + i + " " + str(m))
        common_lib.sleep_wrap(rc, cause="main_sleep")
        
def parse_args():
    QUEUE_PO_DEF = "work:queue:PO"
    QUEUE_PI_BASE_DEF = "work:queue:PI"
    QUEUE_T_BASE_DEF = "work:queue:TP"
    PROD_TIME_DEF = "3600"
    INDEX_PROD_DEF = 0
    RAND_SEED_DEF = 10

    parser = argparse.ArgumentParser(description='Command arguments')
    parser.add_argument("-q", "--queue_po", dest = "queue_po", help = "queue_po value (default is " + str(QUEUE_PO_DEF) + ")", default = QUEUE_PO_DEF, type = str)
    parser.add_argument("-Q", "--queue_pi_base", dest = "queue_pi_base", help = "queue_pi_base value (default is " + str(QUEUE_PI_BASE_DEF) + ")", default = QUEUE_PI_BASE_DEF, type = str)
    parser.add_argument("-t", "--queue_t_base", dest = "queue_t_base", help = "queue_t_base value (default is " + str(QUEUE_T_BASE_DEF) + ")", default = QUEUE_T_BASE_DEF, type = str)
    parser.add_argument("-p", "--prod_time", dest = "prod_time", help = "prod_time value (default is " + str(PROD_TIME_DEF) + ")", default = PROD_TIME_DEF, type = str)
    parser.add_argument("-r", "--rand_seed", dest = "rand_seed", help = "rand_seed value (default is " + str(RAND_SEED_DEF) + ")", default = RAND_SEED_DEF, type = int)
    parser.add_argument("-i", "--index_prod", dest = "index_prod", help = "index_prod value (default is " + str(INDEX_PROD_DEF) + ")", default = INDEX_PROD_DEF, type = int)
    parser.add_argument("redishost", help = "redishost", type = str)
    parser.add_argument("redisport", help = "redisport", type = str)

    common_lib.print_cmd_line(sys.argv)
    args = parser.parse_args()

    if args.queue_po == "":
        print("Error: queue_po (-q) must not be the empty string")
        sys.exit(2)

    if args.queue_pi_base == "":
        print("Error: queue_pi_base (-Q) must not be the empty string")
        sys.exit(2)

    if args.queue_t_base == "":
        print("Error: queue_t_base (-t) must not be the empty string")
        sys.exit(2)

    if args.prod_time == "":
        print("Error: prod_time (-p) must not be the empty string")
        sys.exit(2)

    if args.index_prod < 0:
        print("Error: index_prod (-i) must not be negative")
        sys.exit(2)

    common_lib.print_all_options(args)
    return args

if __name__ == "__main__":
    main()
