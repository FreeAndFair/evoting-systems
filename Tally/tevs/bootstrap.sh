#!/bin/sh

cd ~/tevs/Imaging-1.1.7
python setup.py build_ext -i 2>&1 >/dev/null
cp -a PILB ..

cat ../tevs/docs/db.schema | psql 2>/dev/null
