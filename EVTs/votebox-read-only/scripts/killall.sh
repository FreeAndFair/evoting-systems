#!/bin/sh

for x in 1 2 3 4 5 6 7 8; do
	echo "killing $x"
	ssh -fn sysrack0$x "killall java"
	#sleep 1
done
