#!/bin/sh

inputdata=logdata/e4-supervisor.log

plugin=votebox.auditoriumverifierplugins.IncrementalAuditoriumLogFast

if [ -z "$1" ]; then
	RUNS="0 1 2 4 8 16 32 64 128"
else
	RUNS="$@"
fi

date=`date +%Y%m%d`
host=`hostname`

dirstem=fastbfs-cache
x=1
while [ -e $dirstem-$x ]; do
	((x=$x+1))
done

outdir=$dirstem-$x

mkdir $outdir

echo "saving files to $outdir"

for i in $RUNS; do
	echo "run: $i"
	out=$outdir/incr-${i}.txt

	echo "##################################################" > $out
	echo "# incremental step verifier with fast DAG search; incr=${i}" >> $out
	echo "# by $USER@$host on $date" >> $out
	echo "##################################################" >> $out

	java -cp build verifier.IncrementalStepVerifier incr=${i} \
		rule=rules/voting2.rules \
		log=$inputdata \
		plugin=$plugin \
		>> $out

done
#qtplay /Users/dsandler/Library/Sounds/Babylon\ 5\ Door.aif
