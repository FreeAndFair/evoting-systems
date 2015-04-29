#!/bin/sh
rm -f outimages/*.jpg
for i in images/*.jpg
do
    python wbt.py "$i" $1
done
