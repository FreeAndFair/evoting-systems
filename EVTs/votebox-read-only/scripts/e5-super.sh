#!/bin/sh

EXPT=e5

mkdir -p output conf

conf=conf/$EXPT-supervisor.conf

printf "LOG_LOCATION\nlogdata/$EXPT-supervisor.log\n" > $conf

# 10 hour experiment with 2 minute startup: 10 * 60 * 60 * 1000 + 120000
# ballots every 1 seconds - 2 seconds.

echo "Experiment: $EXPT" > output/$EXPT-supervisor.txt

/usr/java/jdk1.5.0_06/bin/java -cp . sim.pseupervisor.Pseupervisor \
	open-polls-time=120000 \
	close-polls-time=36120000 \
	auth-period-min=1000 auth-period-max=2000 \
	conf=$conf \
	>> output/$EXPT-supervisor.txt
