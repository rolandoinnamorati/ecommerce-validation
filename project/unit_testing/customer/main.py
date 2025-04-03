import common_lib
import sys
import argparse
import datetime
import os
import json
import redis
import more_itertools
import random
import math

def main():
    args = parse_args()
    common_lib.init_rand(args.rand_seed)
    rc = redis.Redis(host=args.redishost, port=args.redisport, decode_responses=True)
    fun_name = "customer_env_" + str(args.index_cust)
    # common_lib.init_time(rc, False, fun_name)
    common_lib.redis_command(rc, "LPUSH " + args.queue_co + " init " + str(args.index_cust))
    resp = common_lib.redis_command(rc, "BRPOP " + args.queue_ci_base + str(args.index_cust) + " 0")[1]
    res = resp.split()
    # print("DBG" + str(res))
    index_cust_db = res[0]
    I = {}
    for i in range(1, len(res), 2):
        I[int(res[i])] = int(res[i + 1])
    print("Availability: " + str(I))
    J = pick_subset(list(I.keys()), args.min_items, args.max_items)
    print("Picked: " + str(J))
    sys.stdout.flush()
    send = ""
    num = 0
    for j in J:
        if I[j] > 0: # and random.uniform(0, 1) > 1 - args.f:
            send += str(j) + " " + str(random.randint(1, I[j])) + " " + str(index_cust_db) + " " + str(args.index_cust) + "|"
            num += 1
    if send != "":
        common_lib.sleep_wrap(rc, cause="think_time")
        send = str(num) + "|" + send[:-1]
        common_lib.redis_command(rc, "LPUSH " + args.queue_co + " " + send)
        common_lib.redis_command(rc, "BRPOP " + args.queue_ci_base + str(args.index_cust) + " 0")
    common_lib.terminate_time(rc)
    print(common_lib.fun_name_glob + " exited normally")
    sys.stdout.flush()

def pick_subset(I, minl, maxl):
    hm = random.randint(min(len(I), minl), min(len(I), maxl))
    ret = []
    for i in range(hm):
        while True:
            pick = random.choice(I)
            if pick not in ret:
                ret += [pick]
                break
    return ret

def parse_args():
    QUEUE_CO_DEF = "work:queue:CO"
    QUEUE_CI_BASE_DEF = "work:queue:CI"
    INDEX_CUST_DEF = 0
    MIN_ITEMS_DEF = 5
    MAX_ITEMS_DEF = 10
    RAND_SEED_DEF = 10

    parser = argparse.ArgumentParser(description='Command arguments')
    parser.add_argument("-r", "--rand_seed", dest = "rand_seed", help = "rand_seed value (default is " + str(RAND_SEED_DEF) + ")", default = RAND_SEED_DEF, type = int)
    parser.add_argument("-q", "--queue_co", dest = "queue_co", help = "queue_co value (default is " + str(QUEUE_CO_DEF) + ")", default = QUEUE_CO_DEF, type = str)
    parser.add_argument("-Q", "--queue_ci_base", dest = "queue_ci_base", help = "queue_ci_base value (default is " + str(QUEUE_CI_BASE_DEF) + ")", default = QUEUE_CI_BASE_DEF, type = str)
    parser.add_argument("-i", "--index_cust", dest = "index_cust", help = "index_cust value (default is " + str(INDEX_CUST_DEF) + ")", default = INDEX_CUST_DEF, type = int)
    parser.add_argument("-m", "--min_items", dest = "min_items", help = "min_items value (default is " + str(MIN_ITEMS_DEF) + ")", default = MIN_ITEMS_DEF, type = int)
    parser.add_argument("-M", "--max_items", dest = "max_items", help = "max_items value (default is " + str(MAX_ITEMS_DEF) + ")", default = MAX_ITEMS_DEF, type = int)
    parser.add_argument("redishost", help = "redishost", type = str)
    parser.add_argument("redisport", help = "redisport", type = str)

    common_lib.print_cmd_line(sys.argv)
    args = parser.parse_args()

    if args.queue_co == "":
        print("Error: queue_co (-q) must not be the empty string")
        sys.exit(2)

    if args.queue_ci_base == "":
        print("Error: queue_ci_base (-Q) must not be the empty string")
        sys.exit(2)

    if args.min_items <= 0:
        print("Error: min_items (-m) must be positive")
        sys.exit(2)

    if args.max_items <= 0:
        print("Error: max_items (-M) must be positive")
        sys.exit(2)

    if args.max_items < args.min_items:
        print("Error: max_items (-M) must not be less than min_items (-m)")
        sys.exit(2)

    if args.index_cust < 0:
        print("Error: index_cust (-i) must not be negative")
        sys.exit(2)

    common_lib.print_all_options(args)
    return args

if __name__ == "__main__":
    main()
