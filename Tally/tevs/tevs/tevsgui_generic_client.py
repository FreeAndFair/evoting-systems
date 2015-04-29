import sys
import time
def do_echo():
    while True:
        print "20 OK 30"
        #print "[--->"
        sys.stdout.flush()
        
        x = sys.stdin.readline()
        print x
        sys.stdout.flush()
        # print raw_input()
        #if x.startswith("x"):
        #    break

if __name__ == "__main__":
    print "Hello"
    sys.stdout.flush()
    print "Goodbye"
    sys.stdout.flush()
    do_echo()
