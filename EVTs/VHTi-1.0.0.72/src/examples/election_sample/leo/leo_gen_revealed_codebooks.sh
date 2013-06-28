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
   echo "Usage: leo_gen_revealed_codebooks.sh NUMBER_TRUSTEES CODE_BIT_LENGTH ELECTION_ID PRECINCT_ID"
   exit 2
fi
n=$1
vcbitlen=$2
eid=$3
pid=$4
vcencoding="<AlphabetEncoding>HEX</AlphabetEncoding>"

# Check revealed codebook secrets
echo "LEO: checking codebook revealed secrets ... "
tid=1
while test $tid -le $n ; do
   echo -n "   TRUSTEE $tid ... "
   vhti_call check_dictionary_secrets \
      ../transcript/precinct_$eid-$pid/tabulation/revealed_codebook_secrets_trustee_$tid.xml \
      ../transcript/precinct_$eid-$pid/config/codebook_commitments_trustee_$tid.xml \
      ../transcript/config/public_key_trustee_$tid.xml \
      ../transcript/precinct_$eid-$pid/config/blank_ballot.xml \
      ./_result.xml
   if test "$(cat _result.xml)" != "<CheckResults>Revealed Dictionary Secrets Check Success</CheckResults>" ; then
      echo -n "FAILED: "
      cat _result.xml
      exit 2
   fi
   echo "done."
   tid=`expr $tid + 1`
done
echo "... done checking codebook revealed secrets."

# Generating revealed codebooks
echo -n "LEO: generating revealed codebook ... "
vhti_call combine_dictionary_secrets \
   ../transcript/precinct_$eid-$pid/tabulation/trustee_revealed_codebook_secrets_box.xml \
   ../transcript/precinct_$eid-$pid/config/blank_ballot.xml \
   $vcbitlen \
   $vcencoding \
   ../transcript/precinct_$eid-$pid/tabulation/trustee_revealed_codebooks.xml
echo "done."

# Clean-up
rm -f ./_*