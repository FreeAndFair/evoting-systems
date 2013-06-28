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
if test $# -lt 2 ; then
   echo "Usage: leo_gen_blank_ballot.sh ELECTION_ID PRECINCT_ID"
   exit 2
fi
eid=$1
pid=$2
vcencoding="<AlphabetEncoding>HEX</AlphabetEncoding>"

# Add prefix/suffix to blank_ballot_skeleton_raw.xml
echo "<BallotSkeleton>" > ./_bs.xml
echo "<ElectionID>$eid</ElectionID>" >> ./_bs.xml
echo "<PrecinctID>$pid</PrecinctID>" >> ./_bs.xml
cat ./ballots/bb_skeleton_$eid-$pid.xml >> ./_bs.xml
echo "</BallotSkeleton>" >> ./_bs.xml

# Generate blank ballot
echo -n "LEO: generating Blank Ballot for Election $eid, Precinct $pid ... "
vhti_call generate_blank_ballot \
   ./_bs.xml \
   ../transcript/config/crypto_election_parameters.xml \
   $vcencoding \
   ./_bb.xml
cp ./_bb.xml ../transcript/precinct_$eid-$pid/config/blank_ballot.xml
echo "done."

# Generate SignedBlankBallot
echo -n "LEO: generating Signed Blank Ballot for Election $eid, Precinct $pid ... "
vhti_call sign_xml \
   ./private_key_leo.xml \
   ./_bb.xml \
   ./blank_ballot_signed.xml
mv ./blank_ballot_signed.xml ../transcript/precinct_$eid-$pid/config
echo "done."

# Clean-up
rm -f ./_*
