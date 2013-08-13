#!/bin/sh

EXPT=e5

scriptdir=scripts
startdir=/home/derrley/votebox

echo "starting supervisor"
sh $scriptdir/$EXPT-super.sh &
disown %

sleep 1

for x in 1 2 3 4 5 6 7 8; do
	echo "starting $x"
	ssh -fn sysrack0$x "$startdir/$scriptdir/$EXPT-booth.sh"
	sleep 1
done
