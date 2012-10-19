#!/bin/bash
# Scantegrity Process Monitor
# Richard Carback < carback1@umbc.edu >

NAME = "scantegrity"
INIT = "/etc/init.d"
PIDNAME = "/var/run/$NAME.pid"
PGREP="/usr/bin/pgrep"

RESTART=0;

# IS the PID running?
kill -0 `cat $PIDNAME`
if [ $? -eq 0 ] then;
	RESTART=1;
fi
# Is there a "java" running?
$PGREP java
if [ $? -ne 0 ] then;
	RESTART=1;
fi
# Is there a "saned" running?
$PGREP saned
if [ $? -ne 0 ] then;
	RESTART=1;
fi

if [ $RESTART -eq 1 ] then;
 # restart
 $INIT/$NAME restart
fi