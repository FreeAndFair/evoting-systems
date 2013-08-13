#!/bin/bash

export CLASSPATH=.

java verifier.Verifier rule=rules/node.rules log=logdata/e4-supervisor.log config=config

