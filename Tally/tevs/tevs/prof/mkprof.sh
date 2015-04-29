#!/bin/sh

for i in `seq 30`
do
    make reset
    #rm -f ~/data/templates/*
    ./main.py $i
done

