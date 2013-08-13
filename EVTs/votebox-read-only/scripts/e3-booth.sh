#!/bin/sh

cd /home/dsandler/develop/votebox

this_rack=`hostname -s|cut -d0 -f2`

conf=conf/e3-booth-$this_rack.conf

#experiment 3: votes cast anywhere from 1 to 10 minutes

mkdir -p output conf

printf "LOG_LOCATION\nlogdata/e3-booth-$this_rack.log\n" > $conf

echo "Running with ID $this_rack"
java -cp build sim.autobooth.Booth id=$this_rack \
	vote-min-time=60000 \
	vote-max-time=600000 \
	conf=$conf \
	> output/e3-booth-$this_rack.txt
