#!/bin/sh

cd /home/dsandler/develop/votebox

this_rack=`hostname -s|cut -d0 -f2`

#votes cast anywhere from 30 seconds to 10 minutes

mkdir -p output

echo "Running with ID $this_rack"
java -cp build sim.autobooth.Booth id=$this_rack \
	vote-min-time=60000 \
	vote-max-time=600000 \
	> output/e2-$this_rack.txt
