#!/bin/sh

mkdir -p output conf

conf=conf/e3-supervisor.conf

printf "LOG_LOCATION\nlogdata/e3-supervisor.log\n" > $conf

# 8 hour experiment with 2 minute startup: 8 * 60 * 60 * 1000 + 120000
# ballots every 15 seconds - 10 min.

java -cp build sim.pseupervisor.Pseupervisor \
	open-polls-time=120000 \
	close-polls-time=28920000 \
	auth-period-min=15000 auth-period-max=600000 \
	conf=$conf \
	> output/e3-supervisor.txt
