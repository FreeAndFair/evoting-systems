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
   echo "Usage: trustee_shuffle.sh TRUSTEE_ID TRUSTEE_ID_LAST ELECTION_ID PRECINCT_ID"
   exit 2
fi
tid=$1
tidlast=$2
eid=$3
pid=$4

# Shuffle raw ballot box
echo -n "TRUSTEE $tid: shuffling from raw_ballot_box_$tidlast to raw_ballot_box_$tid ... "
vhti_call shuffle \
   ../transcript/precinct_$eid-$pid/tabulation/raw_ballot_box_$tidlast.xml \
   ./random_state.xml \
   ../transcript/precinct_$eid-$pid/config/blank_ballot_signed.xml \
   ../transcript/config/public_key_leo.xml \
   ../transcript/precinct_$eid-$pid/tabulation/raw_ballot_box_$tid.xml ./random_state.xml \
   ../transcript/precinct_$eid-$pid/tabulation/shuffle_validity_proof_$tidlast-$tid.xml
echo "done."

# Check shuffle validity proof on raw ballot box
echo -n "TRUSTEE $tid: checking shuffle proof from raw_ballot_box_$tidlast to raw_ballot_box_$tid ... "
vhti_call check_shuffle \
   ../transcript/precinct_$eid-$pid/tabulation/raw_ballot_box_$tidlast.xml \
   ../transcript/precinct_$eid-$pid/tabulation/raw_ballot_box_$tid.xml \
   ../transcript/precinct_$eid-$pid/config/blank_ballot_signed.xml \
   ../transcript/config/public_key_leo.xml \
   ../transcript/precinct_$eid-$pid/tabulation/shuffle_validity_proof_$tidlast-$tid.xml \
   ./_result.xml
if test "$(cat _result.xml)" != "<CheckResults>0:Success</CheckResults>" ; then
   echo -n "FAILED: "
   cat _result.xml
   exit 2
fi
echo "done."

# Clean-up
rm -f ./_*
