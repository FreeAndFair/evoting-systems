import optparse
from os.path import join as pathjoin

def totaltime(filename):
    f = open(filename, 'r')
    start_time = 0
    end_time = 0
    for line in f.readlines():
        if 'init' in line:
            start_time = float(line.split(' ')[1])
        elif 'done' in line:
            end_time = float(line.split(' ')[1])
    print 'Total time (secs):', end_time - start_time
    print '           (mins):', (end_time - start_time) / 60.0
    print '          (hours):', (end_time - start_time) / 3600.0
            
def totaltime_tempmatch(filename):
    f = open(filename, 'r')
    totaltime = 0.0
    for line in f.readlines():
        if 'Time elapsed' in line:
            totaltime += float(line.split(' ')[-1])
    print 'Total time (secs):', totaltime
    print '           (mins):', totaltime / 60.0
    print '          (hours):', totaltime / 3600.0

def main():
    usage = "usage: python get_times.py projects/PROJNAME"
    desc = "Outputs the CPU time for TemplateMatching and Target Extraction."
    parser = optparse.OptionParser(usage=usage, description=desc)
    options, args = parser.parse_args()
    projdir = ''
    if len(args) < 1:
        print "Error - must provide the project directory."
        parser.print_usage()
        exit(1)
    else:
        projdir = args[0]
    tempmatch_file = pathjoin(projdir, 'tempmatch_timing.log')
    runtargets_file = pathjoin(projdir, 'timing_runtarget')

    print "="*32
    print "Select and Group Targets CPU Time \n(i.e. TemplateMatching)"
    print "="*32
    try:
        totaltime_tempmatch(tempmatch_file)
    except IOError:
        print "Couldn't open file {0} - perhaps it doesn't exist?".format(tempmatch_file)

    print

    print "="*32
    print "Run page CPU time \n(i.e. target extraction)"
    print "="*32
    try:
        totaltime(runtargets_file)
    except IOError:
        print "Couldn't open file {0} - perhaps it doesn't exist?".format(runtargets_file)

if __name__ == '__main__':
    main()
