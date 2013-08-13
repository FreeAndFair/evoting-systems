#!/bin/bash

export CLASSPATH=.

time java -Xrunjmp:noobjects,nomonitors verifier.Verifier rule=rules/voting2-q.rules log=logdata/e4-supervisor.log config=config
