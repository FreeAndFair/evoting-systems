#!/bin/sh

for i in `ls -1 ../*.py | xargs -n1 basename | sed '
    /__/d
    /_test/d
    /conf.py/d
    /demo_utils.py/d
    s/\.py$//' | sort | uniq`
do
    cat <<EOF >$i.rst
$i module documentation
=============================================

.. automodule:: $i
   :members:
   :undoc-members:
EOF
done
