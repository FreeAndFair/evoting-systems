import sys
def do_echo():
    while True:
        x = raw_input("-->")
        print x
        sys.stdout.flush()
        if x.startswith("x"):
            break

if __name__ == "__main__":
    print "Hello"
    do_echo()
    print "Goodbye"
