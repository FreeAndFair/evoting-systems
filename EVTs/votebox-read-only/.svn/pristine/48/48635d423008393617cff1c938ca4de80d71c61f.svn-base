#!/bin/sh

EXPT=e4

scriptdir=./scripts
startdir=`pwd`

echo "starting supervisor"
sh $scriptdir/$EXPT-super.sh &
disown %

sleep 1

for x in 1 2 3 4 5 6 7 8; do
	echo "starting $x"
	ssh -fn sysrack0$x "$startdir/$scriptdir/$EXPT-booth.sh"
	sleep 1
done
