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
set -e 

# Usage
if test $# -lt 4 ; then
   echo "Usage: leo_gen_bsn.sh ELECTION_ID PRECINCT_ID NUMBER_OF_BALLOTS NUMBER_OF_PROVISIONAL_BALLOTS"
   exit 2
fi
eid=$1
pid=$2
nb=$3
np=$4

# Generate BSNs
echo -n "LEO: generating $nb BSNs and $np provisional BSNs for Election $eid, Precinct $pid ... "
vhti_call generate_bsns \
   "<ElectionID>$eid</ElectionID>" \
   "<PrecinctID>$pid</PrecinctID>" \
   $nb \
   $np \
   ./random_state.xml \
   ./bsn.xml ./bsnp.xml ./random_state.xml
mv ./bsn.xml ../transcript/precinct_$eid-$pid/config
mv ./bsnp.xml ../transcript/precinct_$eid-$pid/config
echo "done."

# Clean-up
rm -f ./_*
