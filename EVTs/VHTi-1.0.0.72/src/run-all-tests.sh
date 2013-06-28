#!/bin/bash
# 
# This material is subject to the VoteHere Source Code Evaluation
# License Agreement ("Agreement").  Possession and/or use of this
# material indicates your acceptance of this Agreement in its entirety.
# Copies of the Agreement may be found at www.votehere.net.
# 
# Copyright 2004 VoteHere, Inc.  All Rights Reserved
# 
# You may not download this Software if you are located in any country
# (or are a national of a country) subject to a general U.S. or
# U.N. embargo or are deemed to be a terrorist country (i.e., Cuba,
# Iran, Iraq, Libya, North Korea, Sudan and Syria) by the United States
# (each a "Prohibited Country") or are otherwise denied export
# privileges from the United States or Canada ("Denied Person").
# Further, you may not transfer or re-export the Software to any such
# country or Denied Person without a license or authorization from the
# U.S. government.  By downloading the Software, you represent and
# warrant that you are not a Denied Person, are not located in or a
# national of a Prohibited Country, and will not export or re-export to
# any Prohibited Country or Denied Party.

brunch_root=$(cd $(dirname $0)/..; pwd)
date

set -e

# Resist the tempation to replace these curly-braces with parens.
# Were you to do so, this script would continue despite any failure
# from the contained commands.

{
    pushd $brunch_root/src/vhti/bindings/perl

    perl ./Makefile.PL
    make
    cd examples
    ./womb-to-tomb.sh
    cd ..
    ./examples/go.sh make test

    {
        pushd ../../../examples/election_sample
        ./_runall.sh
        popd > /dev/null
    }

    popd > /dev/null
}

# Gotta do the perl examples before these, because these read XML
# files that those perl examples generate.

if true; then

    echo -n running XML tests ''
    $brunch_root/src/xml-tests.sh

    echo -n running samples\; this takes a while ... ''

    $brunch_root/src/samples.sh &> /tmp/spew        || { echo Some sample failed. ; cat -n /tmp/spew | tail; exit 1; }

    echo done
fi

cd $brunch_root/src/vhti/bindings/perl

{
    pushd examples

    rm -f stats || true

    ./many-answer-marks.sh
    popd > /dev/null
}

make clean

echo Consider using \`valgrind\' or \`mpatrol\' to check for memory
echo leaks.
