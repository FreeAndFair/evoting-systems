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

here=$(cd $(dirname $0); pwd)
export PERL5LIB=$here/..
export LD_LIBRARY_PATH=$PERL5LIB/blib/arch/auto/VHTI
PATH=$PATH:.

# If you change this to `false', then you'll probably also want to
# edit ../Makefile.PL, and change the paths in OBJECT to point to
# debug versions
if true; then
    vhti=$here/../../../lib
    poll=$here/../../../../vhti_internal/src/vhti_pollsite_dll/Release
else
    vhti=$here/../../../lib/Debug
    poll=$here/../../../../vhti_internal/src/vhti_pollsite_dll/Debug
fi

PATH=$PATH:$vhti:$poll

time "$@"
