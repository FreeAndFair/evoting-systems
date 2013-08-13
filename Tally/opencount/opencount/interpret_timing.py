"""
A script to parse the results of the OpenCount timing log files (created
via the --time option).
Intended to be used for the EVT/WOTE 2013 paper submission, to easily
generate relevant timing information from the raw timing log files.
"""

USAGE = """Usage:
    python interpret_timing.py [-h --help -help] TIMING_LOGFILE
"""

import sys, pdb, collections

def parse_logfile(filepath):
    """ Timing Logfiles are of the form:
    ================
    Beginning new log session, on:
    YEAR-MONTH-DAY HOUR:MINUTE:SECOND
    ================
    Task 'TASKNAME_0':
        TIME_0 seconds
    Task 'TASKNAME_1':
        TIME_1 seconds
    ...
    """
    f = open(filepath)
    lines = f.readlines()
    i = 0
    timings = collections.OrderedDict() # maps {str task: float time}
    while i < len(lines):
        line = lines[i]
        if not line or not line.strip():
            i += 1
            continue
        line = line.strip()
        if line[0] == '=':
            # Skip the header
            i += 4
            continue
        if not line.startswith("Task"):
            print "Woah, line doesn't begin with Task?!"
            print line
            pdb.set_trace()
            print "Fatal Error: Invalid logfile format. Exiting."
            exit(1)
        task = line[6:-2] # Task '<FOO>': -> <FOO>
        if i == len(lines) - 1:
            print "Woah, Task definition doesn't have associated time declaration?!"
            print line
            pdb.set_trace()
            print "Fatal Error: Invalid logfile format. Exiting."
            exit(1)
        if lines[i+1].strip() == 'UNKNOWN':
            timings[task] = 'UNKNOWN'
        else:
            time = float(lines[i+1].strip().replace(' seconds', ''))
            timings[task] = time
        i += 2
    return timings

def main():
    args = sys.argv[1:]
    if '-h' in args or '--help' in args or '-help' in args:
        print USAGE
        exit(0)

    if len(args) == 0:
        print "Fatal Error: Must pass in TIMING_LOGFILE path."
        print USAGE
        exit(1)

    filepath = args[-1]
    
    timings = parse_logfile(filepath)

    total_acc = 0

    for task, dur in timings.iteritems():
        print "'{0}': {1}".format(task, dur)
        if task.endswith("_Total"):
            if dur != 'UNKNOWN':
                total_acc += dur

    print "Total_acc:", total_acc

if __name__ == '__main__':
    main()
