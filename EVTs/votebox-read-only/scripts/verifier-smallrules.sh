#!/bin/sh

inputdata=logdata/e4-supervisor.log

plugin=votebox.auditoriumverifierplugins.IncrementalAuditoriumLog

rules=rules/voting-small-2.rules

cache=true

restart=true

echo "be sure to set USE_CACHE to $cache"

if [ -z "$1" ]; then
	RUNS="0 1 2 4 8 16 32 64 128"
else
	RUNS="$@"
fi

date=`date +%Y%m%d`
host=`hostname`

if [ "$cache" = "true" ]; then
	dirstem=cache
else
	dirstem=nocache
fi

if [ "$restart" = "true" ]; then
	dirstem="monolithic-$dirstem"
fi

dirstem="small-2-$dirstem"

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
	echo "# incremental step verifier; DAGcache: $cache; incr=${i}" >> $out
	echo "# restart=$restart ; rule=$rules ; plugin=$plugin" >> $out
	echo "# by $USER@$host on $date" >> $out
	echo "##################################################" >> $out

	java -cp build verifier.IncrementalStepVerifier incr=${i} \
		rule=$rules \
		log=$inputdata \
		plugin=$plugin \
		restart=$restart \
		>> $out

done
#qtplay /Users/dsandler/Library/Sounds/Babylon\ 5\ Door.aif
