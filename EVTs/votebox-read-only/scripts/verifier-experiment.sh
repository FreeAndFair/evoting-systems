#!/bin/sh

inputdata=logdata/e4-supervisor.log

if [ -z "$1" ]; then
	RUNS="0 1 2 4 8 16 32 64 128"
else
	RUNS="$@"
fi

date=`date +%Y%m%d`
host=`hostname`

for i in $RUNS; do
	out=incr-${i}.txt

	echo "##################################################" > $out
	echo "# incremental step verifier; incr=${i}" >> $out
	echo "# by $USER@$host on $date" >> $out
	echo "##################################################" >> $out

	java -cp build verifier.IncrementalStepVerifier incr=${i} \
		rule=rules/voting2.rules \
		log=$inputdata \
		plugin=votebox.auditoriumverifierplugins.IncrementalAuditoriumLog \
		>> $out

done
#qtplay /Users/dsandler/Library/Sounds/Babylon\ 5\ Door.aif
