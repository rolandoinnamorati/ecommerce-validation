import psycopg2
import os
import sys
import redis
import time
import random
import datetime

QUEUE_PREFIX = "work:queue:"
QUEUE_INIT_BARR_SEND = "work:queue:INIT_BARR_SEND"
CONFIG_FILE_PATH = "../config.txt"
SIMULATION_MODE = True

fun_name_glob = ""
advance_elapsed_glob = 0
also_barrier_glob = False

def init_time(rc, also_register, fun_name):
    global advance_elapsed_glob
    global curr_elapsed_glob
    global conn_env_glob
    global db_env_glob
    global conn_redis_log_glob
    global db_redis_log_glob
    global fun_name_glob
    global starting_int_glob
    global excl_glob
    global before_glob
    global also_barrier_glob
    global also_answer_glob
    global after_but_empty_glob
    before_glob = False
    also_barrier_glob = False
    starting_int_glob = -1
    fun_name_glob = fun_name
    f = open(CONFIG_FILE_PATH, "r")
    content = f.read().splitlines()
    f.close()
    (conn_env_glob, db_env_glob) = db_connect("dbname=%s user=%s password=%s host=%s port=%s" %(content[0], content[1], content[2], content[3], content[4]))
    if SIMULATION_MODE:
        (conn_redis_log_glob, db_redis_log_glob) = db_connect("dbname=%s user=%s password=%s host=%s port=%s" %(content[5], content[6], content[7], content[8], content[9]))
        excl_glob = []
        #in the environment, random seeds are arguments
        for i in range(10, len(content)):
            if content[i] == "OPTIONS":
                before_glob = (content[i + 1][0] == "1")
                also_barrier_glob = (content[i + 1][1] == "1")
                also_answer_glob = (content[i + 1][2] == "1")
                after_but_empty_glob = (content[i + 1][3] == "1")
                print([before_glob, also_barrier_glob, also_answer_glob, after_but_empty_glob])
                sys.stdout.flush()
            elif content[i] == "EXCL":
                for j in range(i + 1, len(content)):
                    excl_glob += [content[j]]
                break
        if also_register:
            ba_redis_command(rc, also_barrier_glob, "LPUSH %s %s" %(QUEUE_INIT_BARR_SEND, QUEUE_PREFIX + fun_name))
        res = ba_redis_command(rc, also_barrier_glob, "BRPOP %s %d" %(QUEUE_PREFIX + fun_name + "_1", 0))
        res_ar = res[1].split()
        starting_int_glob = float(res_ar[0])
        advance_elapsed_glob = 0
        curr_elapsed_glob = float(res_ar[1])

def terminate_time(rc):
    global conn_env_glob
    global db_env_glob
    global conn_redis_log_glob
    global db_redis_log_glob
    global fun_name_glob
    global also_barrier_glob
    if SIMULATION_MODE:
        base_channel = QUEUE_PREFIX + fun_name_glob
        ba_redis_command(rc, also_barrier_glob, "LPUSH %s %s" %(base_channel + "_0", "TERM"))
        ba_redis_command(rc, also_barrier_glob, "BRPOP %s %d" %(base_channel + "_1", 0))
        db_redis_log_glob.close()
        conn_redis_log_glob.close()
    db_env_glob.close()
    conn_env_glob.close()

def ba_redis_command(rc, also_wrap, cmd, cmd_alt=None):
    global before_glob
    global also_answer_glob
    global after_but_empty_glob
    cmd_ar = cmd.split()
    if also_wrap and before_glob:
        also_send_to_psql("before", "%s" %(cmd_alt if cmd_alt != None else cmd))
    #ret = rc.execute_command(cmd)
    if cmd_ar[0] == "LLEN" or cmd_ar[0] == "LRANGE":
        ret = rc.llen(cmd_ar[1])
    elif cmd_ar[0] == "LPUSH":
        msg = cmd[len(cmd_ar[0]) + 1 + len(cmd_ar[1]) + 1:]
        rc.lpush(cmd_ar[1], msg)
        ret = None
    elif cmd_ar[0] == "RPOP":
        ret = rc.rpop(cmd_ar[1])
    elif cmd_ar[0] == "BRPOP":
        ret = rc.brpop(cmd_ar[1], 0)
    if also_wrap and (cmd_ar[0] != "RPOP" or after_but_empty_glob or ret != None):
        if cmd_ar[0] == "RPOP" and ret == None:
            msg = "after but empty"
        else:
            msg = "after"
        if also_answer_glob and (cmd_ar[0] == "BRPOP" or (cmd_ar[0] == "RPOP" and ret != None)):
            if cmd_ar[0] == "BRPOP":
                recv = ret[1]
            elif type(ret) == str:
                recv = ret
            else:
                recv = ""
                for r in ret:
                    recv = recv + "|||" + r
            also_send_to_psql(msg, "%s RECV: %s" %(cmd_alt if cmd_alt != None else cmd, recv))
        else:
            also_send_to_psql(msg, "%s" %(cmd_alt if cmd_alt != None else cmd))
    return ret

def redis_command(rc, cmd):
    global advance_elapsed_glob
    global curr_elapsed_glob
    global fun_name_glob
    global also_barrier_glob
    cmd_ar = cmd.split()
    if SIMULATION_MODE:
        base_channel = QUEUE_PREFIX + fun_name_glob
        sync_sleep(rc)
        if cmd_ar[0] == "LLEN":
            ba_redis_command(rc, True, cmd)
            lump_time(rc, cause="poll")
            return tmp
        if cmd_ar[0] == "RPOP" or cmd_ar[0] == "LPUSH":
            if cmd_ar[0] != "LPUSH" or cmd_ar[1] != QUEUE_INIT_BARR_SEND:
                if cmd_ar[0] == "RPOP":
                    other = "|" + ("1" if len(cmd_ar) == 2 else str(cmd_ar[2]))
                else:
                    other = ""
                ba_redis_command(rc, also_barrier_glob, "LPUSH %s %s%s%s" %(base_channel + "_0", cmd_ar[0], cmd_ar[1], other))
                ba_redis_command(rc, also_barrier_glob, "BRPOP %s %d" %(base_channel + "_1", 0)) #ACK
            ret = ba_redis_command(rc, True, cmd)
            lump_time(rc, cause=("recv") if cmd_ar[0] == "RPOP" else "send")
            return ret
        if cmd_ar[0] == "BRPOP":
            ba_redis_command(rc, also_barrier_glob, "LPUSH %s %s%s" %(base_channel + "_0", "DROP", cmd_ar[1]))
            #the inside_timestamp of this command (receving an Ltime) will be the old one, unavoidable
            curr_elapsed_glob = float(ba_redis_command(rc, also_barrier_glob, "BRPOP %s %d" %(base_channel + "_1", 0))[1][1:])
            ret = ba_redis_command(rc, True, "BRPOP %s 0" %(cmd_ar[1])) #it may be still the case that the message is not sent (of course, it will be in a very short time)
            ba_redis_command(rc, also_barrier_glob, "LPUSH %s %s" %(base_channel + "_0", "ACK"))
            lump_time(rc, cause="recv")
            return ret
    else:
        if cmd_ar[0] != "LPUSH":
            return(rc.execute_command(cmd))
        msg = cmd[len(cmd_ar[0]) + 1 + len(cmd_ar[1]) + 1:]
        return rc.lpush(cmd_ar[1], msg)
    
def pseudo_barrier(rc, t, qi, qo):
    global also_barrier_glob
    ba_redis_command(rc, also_barrier_glob, "LPUSH %s %lf" %(qi, t))
    res = ba_redis_command(rc, also_barrier_glob, "BRPOP %s %d" %(qo, 0))[1]
    return res[1:]

def init_rand(s):
    random.seed(s)

def also_send_to_psql(ba, msg):
    global db_redis_log_glob
    global advance_elapsed_glob
    global curr_elapsed_glob
    global starting_int_glob
    global excl_glob
    global fun_name_glob
    if msg.split()[0] in excl_glob:
        return
    now = time.time()
    if starting_int_glob == -1: #only for the first messages with init
        sql = "INSERT INTO full_log (ts_exec, ts_epoch, ts, from_function, fulltext) VALUES (%lf, extract(epoch from now()), now() at time zone 'UTC', '%s', '%s %s')" %(now, fun_name_glob, ba, msg)
    else:
        sql = "INSERT INTO full_log (ts_exec, ts_epoch, ts, inside_elapsed, inside_timestamp, from_function, fulltext) VALUES (%lf, extract(epoch from now()), now() at time zone 'UTC', %lf, CAST(TO_TIMESTAMP(%lf) AS TIMESTAMP WITHOUT TIME ZONE), '%s', '%s %s')" %(now, curr_elapsed_glob, starting_int_glob + curr_elapsed_glob, fun_name_glob, ba, msg)
    exec_and_retrieve(db_redis_log_glob, sql, output=False)
    
def sync_sleep(rc):
    global advance_elapsed_glob
    global curr_elapsed_glob
    global fun_name_glob
    if SIMULATION_MODE:
        base_channel = QUEUE_PREFIX + fun_name_glob
        curr_elapsed_glob = float(pseudo_barrier(rc, advance_elapsed_glob, base_channel + "_0", base_channel + "_1"))
        advance_elapsed_glob = 0

def sleep_wrap(rc, cause="", fixed_time=0):
    if SIMULATION_MODE:
        lump_time(rc, cause=cause, fixed_time=fixed_time)
    else:
        lump_time(rc, cause=cause, fixed_time=fixed_time, sleep=True)
        
def lump_time(rc, cause="", fixed_time=0, sleep=False):
    global advance_elapsed_glob
    global db_env_glob
    global fun_name_glob
    if not(hasattr(lump_time, "causes")):
        lump_time.causes = {}
    if cause == "":
        to_be_slept = fixed_time
    else:
        if not(cause in lump_time.causes):
            sql = "SELECT rand_time_type FROM function_time WHERE '%s' SIMILAR TO fname AND statm_type = '%s'" %(fun_name_glob, cause)
            res = exec_and_retrieve(db_env_glob, sql)
            if len(res) == 0:
                print("Error while executing query " + sql)
                assert(0)
            lump_time.causes[cause] = res[0]["rand_time_type"]
        to_be_slept = custom_random(lump_time.causes[cause])
    if not(sleep):
        advance_elapsed_glob += to_be_slept
    else:
        print("Sleeping %d" %to_be_slept)
        sys.stdout.flush()
        time.sleep(to_be_slept)

def custom_random(spec):
    if "finite_uniform" in spec:
        ar = spec.split(":")
        return random.choose([float(v) for v in ar[1:]])
    elif "gaussian" in spec:
        ar = spec.split(":")
        while True:
            val = random.normalvariate(float(ar[1]), float(ar[2]))
            if val > 0:
                break
        return val
    else:
        return float(spec)
    
def db_connect(conn_string):
    try:
        conn = psycopg2.connect(conn_string)
        conn.autocommit = True
        db = conn.cursor()
    except Exception as inst:
        raise Exception("Internal error: failed to connect to db with params " + conn_string + " because of " + str(inst))
    return (conn, db)

def exec_and_retrieve(db, sql, output = True):
    result = []
    try:
        db.execute(sql)
        if (output):
            res = db.fetchone()
            while (res != None):
                result += [{}]
                for j in range(len(db.description)):
                    if (res[j] == None):
                        result[-1][db.description[j].name] = None
                    else:
                        result[-1][db.description[j].name] = res[j]
                res = db.fetchone()
    except Exception as inst:
        raise Exception("Internal error while executing SQL command\n\t" + sql + "\nThe error is:\n\t" + str(inst))
    return result

def str_or_null(x, mode = 'non_apexes'):
    if (x == None):
        return "NULL"
    if (mode == 'apexes'):
        return "'" + str(x) + "'"
    elif (mode == 'timeslot'):
        return "TIMESTAMP '" + str(x) + "' AT TIME ZONE 'UTC'"
        # return "TIMESTAMP '" + str(x).split()[0] + "T" + str(x).split()[1] + "' AT TIME ZONE 'UTC'"
    return str(x)

def print_cmd_line(argv):
    print("Printing command line as typed:")
    cmd_line = ""
    for i in range(len(argv)):
        cmd_line += argv[i] + " "
    print(cmd_line)
    sys.stdout.flush()

def print_all_options(args):
    print("Printing all options with corresponding values:")
    max_len = max([len(arg) for arg in vars(args)])
    for arg in sorted(vars(args)):
        print("\t" + arg + ":" + " "*(max_len - len(arg) + 1) + str(getattr(args, arg)))
    sys.stdout.flush()

def progress(t, max_time):
    print("Elapsed %d out of %d (%.2lf%%)" %(t, max_time, 100*float(t)/max_time))
    sys.stdout.flush()
    
