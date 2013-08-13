#!/bin/sh

EXPT=e5

cd /home/derrley/votebox

this_rack=`hostname -s|cut -d0 -f2`

conf=conf/$EXPT-booth-$this_rack.conf

#experiment 5 (derrley): votes cast anywhere from .5 sec to 1 seconds

mkdir -p output conf

printf "LOG_LOCATION\nlogdata/$EXPT-booth-$this_rack.log\n" > $conf

echo "Running with ID $this_rack"
/usr/java/jdk1.5.0_06/bin/java -cp . sim.autobooth.Booth id=$this_rack \
	vote-min-time=500 \
	vote-max-time=1000 \
	conf=$conf \
	> output/$EXPT-booth-$this_rack.txt
