#!/bin/sh

# tuned for a very short simulation---ballots are cast between 10 and 60
# seconds after authorized

this_rack=`hostname -s|cut -d0 -f2`

echo "Running with ID $this_rack"
java -cp build sim.autobooth.Booth id=$this_rack \
	vote-min-time=10000 \
	vote-max-time=60000
