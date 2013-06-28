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
   echo "Usage: leo_gen_crypto_election_parameters.sh NUMBER_OF_TRUSTEES THRESHOLD"
   exit 2
fi
n=$1
t=$2

# Check election configuration
echo "LEO: checking election configuration ... "
i=1
while test $i -le $n ; do
   perl ../perl/extract_element.pl ../transcript/config/committed_trustee_$i.xml ./_trustee_$i.xml "Authority"
   perl ../perl/extract_element.pl ../transcript/config/committed_trustee_$i.xml ./_key_share_commitment_trustee_$i.xml "KeyShareCommitment"
   echo -n "LEO: checking TRUSTEE $i committments ... "
   vhti_call check_commitment \
      ../transcript/config/key_gen_parameters.xml \
      ./_trustee_$i.xml \
      ../transcript/config/broadcast_values.xml \
      ./_key_share_commitment_trustee_$i.xml \
      ./_result.xml
   if test "$(cat _result.xml)" != "<CheckResults>0:Success</CheckResults>" ; then
      echo -n "FAILED: "
      cat _result.xml
      exit 2
   fi
   
   i=`expr $i + 1`
   echo "done."
done
echo "... done checking election configuration."

# Generate CryptoElectionParameters
echo -n "LEO: generating CryptoElectionParameters ... "
echo "<CryptoElectionParameters>" > ./crypto_election_parameters.xml
cat ../transcript/config/crypto_group_parameters.xml >> ./crypto_election_parameters.xml
echo "<CryptoTabulationParameters>" >> ./crypto_election_parameters.xml
cat ../transcript/config/election_pubkey.xml >> ./crypto_election_parameters.xml
echo "<NumAuth>$n</NumAuth>" >> ./crypto_election_parameters.xml
echo "<Threshold>$t</Threshold>" >> ./crypto_election_parameters.xml

i=1
while test $i -le $n ; do
   cat ../transcript/config/key_share_commitment_trustee_$i.xml >> ./crypto_election_parameters.xml
   echo '' >> ./crypto_election_parameters.xml    # force a line-feed
   rm ../transcript/config/key_share_commitment_trustee_$i.xml
   i=`expr $i + 1`
done

echo "</CryptoTabulationParameters>" >> ./crypto_election_parameters.xml
echo "</CryptoElectionParameters>" >> ./crypto_election_parameters.xml
echo "done."

# Remove redundant data
mv ./crypto_election_parameters.xml ../transcript/config
rm ../transcript/config/key_gen_parameters.xml
rm ../transcript/config/crypto_group_parameters.xml
rm ../transcript/config/election_pubkey.xml

# Generate VoteVerificationKeys
# WARNING: the vote verification keys are sensitive. 
#  In this implementation, we assume that the trustees give their vote verification keys
#  to the LEO. It would be better (for voter privacy) to each trustee load the DRE.
echo "<VoteVerificationKeys>" > ./vote_verification_keys.xml
i=1
while test $i -le $n ; do
   cat ./vote_verification_key_trustee_$i.xml >> ./vote_verification_keys.xml
   rm ./vote_verification_key_trustee_$i.xml
   echo '' >> ./vote_verification_keys.xml    # force a line-feed
   i=`expr $i + 1`
done
echo "</VoteVerificationKeys>" >> ./vote_verification_keys.xml

# Clean-up
rm -f ./_*
