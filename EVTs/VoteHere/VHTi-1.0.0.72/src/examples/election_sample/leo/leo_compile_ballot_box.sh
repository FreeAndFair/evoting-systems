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
   echo "Usage: leo_compile_ballot_box.sh ELECTION_ID PRECINCT_ID"
   exit 2
fi
eid=$1
pid=$2

# Make transcipt ballot box directory
mkdir -p ../transcript/precinct_$eid-$pid/ballotbox
mkdir -p ../transcript/precinct_$eid-$pid/tabulation

# How many ballots were voted?
declare -a ballots=($(ls ../dre/ballotbox_$eid-$pid/*-svb*))
nballots=${#ballots[@]}

# Assume all BSNs were voted, then delete those voted
cp ../transcript/precinct_$eid-$pid/config/bsn.xml ../transcript/precinct_$eid-$pid/tabulation/bsn_unused.xml
cp ../transcript/precinct_$eid-$pid/config/bsnp.xml ../transcript/precinct_$eid-$pid/tabulation/bsnp_unused.xml

# Extract VotedBallot and RawVotedBallot from SignedVoted Ballots
echo "<RawBallotBox>" > ./raw_ballot_box_0.xml
echo "<SignedVotedBallots>" > ./signed_voted_ballots.xml
i=0
while test $i -lt $nballots ; do

   # Extract VotedBallot from SignedVotedBallot
   echo -n "LEO: checking ${ballots[$i]} signature ... "
   vhti_call check_xml \
      ../transcript/config/public_key_dre.xml ${ballots[$i]} \
      \"VotedBallot\" \
      ./_result.xml ./_vb.xml
   if test "$(cat _result.xml)" != "<CheckResults>0:Success</CheckResults>" ; then
      echo -n "FAILED: "
      cat _result.xml
      exit 2
   fi
   echo "done."
   perl ../perl/extract_element.pl ./_vb.xml ./_rb.xml "RawVotedBallot"
   perl ../perl/extract_element.pl ./_vb.xml ./_bsn.xml "BallotSequenceNumber"

   # Save off unused BSNs for codebook audit
   perl ../perl/delete_element_w_value.pl \
      ../transcript/precinct_$eid-$pid/tabulation/bsn_unused.xml _bsn.xml
   perl ../perl/delete_element_w_value.pl \
      ../transcript/precinct_$eid-$pid/tabulation/bsnp_unused.xml _bsn.xml

   # Add RawVotedBallot to RawBallotBox
   cat ./_rb.xml >> ./raw_ballot_box_0.xml
   echo '' >> ./raw_ballot_box_0.xml      # force a line-feed

   # Add SignedVotedBallot to SignedVotedBallots
   cat ${ballots[$i]} >> ./signed_voted_ballots.xml
   echo '' >> ./signed_voted_ballots.xml    # force a line-feed

   echo ""
   i=`expr $i + 1`
done

# Move data into election transcript
cp ../dre/ballotbox_$eid-$pid/results* ../transcript/precinct_$eid-$pid/ballotbox

echo "</RawBallotBox>" >> ./raw_ballot_box_0.xml
cp ./raw_ballot_box_0.xml ../transcript/precinct_$eid-$pid/ballotbox/raw_ballot_box.xml
mv ./raw_ballot_box_0.xml ../transcript/precinct_$eid-$pid/tabulation

echo "</SignedVotedBallots>" >> ./signed_voted_ballots.xml
mv ./signed_voted_ballots.xml ../transcript/precinct_$eid-$pid/ballotbox

# Clean-up
rmdir precinct_$eid-$pid  # BUGBUG: for some reason, unsnarf drops a directory
rmdir tabulation # BUGBUG: for some reason, unsnarf drops a directory
rmdir transcript  # BUGBUG: for some reason, unsnarf drops a directory
rm -f ./_*
