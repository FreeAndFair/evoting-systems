#!/bin/sh

echo Launching TEVS main.py
./main.py $*
echo Launching TEVS summarize.py
sleep .6s
./summarize_results.py $* 
