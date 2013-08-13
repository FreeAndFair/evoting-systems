#!/bin/sh

EXPT=e4

mkdir -p output conf

conf=conf/$EXPT-supervisor.conf

printf "LOG_LOCATION\nlogdata/$EXPT-supervisor.log\n" > $conf

# 8 hour experiment with 2 minute startup: 8 * 60 * 60 * 1000 + 120000
# ballots every 10 seconds - 2 min.

echo "Experiment: $EXPT" > output/$EXPT-supervisor.txt

java -cp build sim.pseupervisor.Pseupervisor \
	open-polls-time=120000 \
	close-polls-time=28920000 \
	auth-period-min=10000 auth-period-max=120000 \
	conf=$conf \
	>> output/$EXPT-supervisor.txt
