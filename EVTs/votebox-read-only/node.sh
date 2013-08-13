#!/bin/bash

export CLASSPATH=.

/usr/java/jdk1.5.0_06/bin/java verifier.Verifier rule=rules/node.rules log=logdata/e4-dup.log config=config

