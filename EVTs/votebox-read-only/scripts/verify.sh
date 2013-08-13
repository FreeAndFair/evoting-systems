#!/bin/sh

if [ -z "$1" ]; then
	echo "usage: $0 [key=value*] input.log"
	exit 1
fi

java -cp build verifier.Verifier \
	rule=rules/voting2.rules \
	config=config \
	log=$log
