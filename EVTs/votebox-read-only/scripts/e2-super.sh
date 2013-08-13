#!/bin/sh

mkdir -p output

# 6 hour experiment
# polls 
# ballots every 1-5 min
java -cp build sim.pseupervisor.Pseupervisor \
	open-polls-time=120000 \
	close-polls-time=21600000 \
	auth-period-min=60000 auth-period-max=300000 \
	conf=supervisor.conf \
	> output/e2-super.txt
