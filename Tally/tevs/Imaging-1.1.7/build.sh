#!/bin/bash

if [ "$1" = "clean" ]; then
  python setup.py clean
  rm -f *.so PIL/*.so
fi

python setup.py build_ext -i
python selftest.py
