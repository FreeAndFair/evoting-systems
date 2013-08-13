#!/bin/sh

log=${log:=logdata/e4-supervisor.log}
plugin=${plugin:=votebox.auditoriumverifierplugins.IncrementalAuditoriumLog}
rules=${rules:=rules/voting2.rules}
dagcache=${dagcache:=true}
restart=${restart:=false}
mainclass=${mainclass:=verifier.IncrementalStepVerifier}
incr=${incr:=0 1 2 4 8 16 32 64 128}

if [ "$1" == '-h' ]; then
	echo "usage: [K=V]* $0 [incr]*"
	echo
	echo "environment variables of interest and their default values: "
	echo "  log=$log"
	echo "  rules=$rules"
	echo "  plugin=$plugin"
	echo "     ...(use IncrementalAuditoriumLog for ExplicitDAG, IncrementalAuditoriumLogFast for FastDAG)"
	echo "  dagcache=$dagcache"
	echo "  restart=$restart (false=incremental; true=monolithic)"
	echo "  mainclass=$mainclass"
	echo "  incr=$incr (increments to run)"
	exit
fi

if [ ! -z "$1" ]; then
	incr="$@"
fi

if echo "$incr" | grep -v '[ 0-9]'; then
    echo "Invalid increments: '$incr'"
    exit 2
fi

date=`date +%Y%m%d`
host=`hostname`

dirstem=run

if [ "$plugin" = "votebox.auditoriumverifierplugins.IncrementalAuditoriumLogFast" ]; then
	dirstem="fastdag-$dirstem"
fi

if [ "$dagcache" = "true" ]; then
	dirstem="dagcache-$dirstem"
else
	dirstem="$dirstem"
fi

if [ "$restart" = "true" ]; then
	dirstem="monolithic-$dirstem"
fi


dirstem="$dirstem"

x=1
while [ -e $dirstem-$x ]; do
	((x=$x+1))
done

outdir="$dirstem-$x"

mkdir $outdir

echo "*** saving files to $outdir"

for i in $incr; do
	echo "run: $i"
	out=$outdir/incr-${i}.txt
	
	echo >$out <<_EOM_
##################################################
# RUN: incremental step verifier -- incr=${i}
#   by $USER@$host on $date
#   main class: $mainclass
# ARGS:
#   restart=$restart ; dagcache=$dagcache
#   plugin=$plugin 
#   log=$log ; rule=$rules
##################################################
_EOM_

	java -cp build $mainclass incr=${i} \
		rule=$rules \
		log=$log \
		plugin=$plugin \
		restart=$restart \
		dagcache=$dagcache \
		>> $out

done
#qtplay /Users/dsandler/Library/Sounds/Babylon\ 5\ Door.aif
