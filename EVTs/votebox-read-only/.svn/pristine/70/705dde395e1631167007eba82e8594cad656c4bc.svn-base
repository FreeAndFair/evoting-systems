#!/bin/sh

EXPT=e4

cd /home/dsandler/develop/votebox

this_rack=`hostname -s|cut -d0 -f2`

conf=conf/$EXPT-booth-$this_rack.conf

#experiment 3: votes cast anywhere from 30 sec to 5 minutes

mkdir -p output conf

printf "LOG_LOCATION\nlogdata/$EXPT-booth-$this_rack.log\n" > $conf

echo "Running with ID $this_rack"
java -cp build sim.autobooth.Booth id=$this_rack \
	vote-min-time=30000 \
	vote-max-time=300000 \
	conf=$conf \
	> output/$EXPT-booth-$this_rack.txt
