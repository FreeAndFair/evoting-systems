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
if test $# -lt 3 ; then
   echo "Usage: trustee_gen_codebook_commitments.sh TRUSTEE_ID ELECTION_ID PRECINCT_ID"
   exit 2
fi
tid=$1
eid=$2
pid=$3

# Check the blank ballot signature in SignedBlankBallot
echo -n "TRUSTEE $tid: checking SignedBlankBallot signature ... "
vhti_call check_xml \
   ../transcript/config/public_key_leo.xml \
   ../transcript/precinct_$eid-$pid/config/blank_ballot_signed.xml \
   \"BlankBallot\" \
   ./_result.xml ./_bb.xml
if test "$(cat _result.xml)" != "<CheckResults>0:Success</CheckResults>" ; then
   echo -n "FAILED: "
   cat _result.xml
   exit 2
fi
echo "done."

# Generate codebook commitments
perl ../perl/extract_element.pl ../transcript/config/committed_trustee_$tid.xml ./_trustee_$tid.xml "Authority"
echo -n "TRUSTEE $tid: generating codebook commitments for Election $eid, Precinct $pid ... "
vhti_call generate_vvdict_commits \
   ./_trustee_$tid.xml \
   ./private_key_trustee_$tid.xml \
   ./vote_verification_key_trustee_$tid.xml \
   ./_bb.xml \
   ../transcript/precinct_$eid-$pid/config/bsn.xml \
   ./codebook_commitments_trustee_$tid.xml
echo "done."
mv ./codebook_commitments_trustee_$tid.xml ../transcript/precinct_$eid-$pid/config

# Clean-up
rm -f ./_*
