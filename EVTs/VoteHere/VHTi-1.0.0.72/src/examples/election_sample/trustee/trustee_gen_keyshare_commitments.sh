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
   echo "Usage: trustee_gen_keyshare_commitments.sh TRUSTEE_ID NUMBER_OF_TRUSTEES"
   exit 2
fi
tid=$1
n=$2

# Concatenate pairwise secrets
echo "<PairwiseSecrets>" > ./_pairwise_secrets_trustee_$tid.xml
i=1
while test $i -le $n ; do
   if test $i -ne $tid ; then
      # Decrypt the transmission from TRUSTEE $i
      echo -n "TRUSTEE $tid: decrypting pairwise_secret_trustee_$i-$tid.xml ... "
      vhti_call decrypt \
         ./private_key_trustee_$tid.xml \
         ./pairwise_secret_encrypted_trustee_$i-$tid.xml \
         ./pairwise_secret_trustee_$i-$tid.xml
      echo "done."
   fi

   # Add to PairwiseSecrets
   cat ./pairwise_secret_trustee_$i-$tid.xml >> ./_pairwise_secrets_trustee_$tid.xml
   echo '' >> ./_pairwise_secrets_trustee_$tid.xml    # force a line-feed

   # Clean-up
   if test $i -ne $tid ; then
      rm ./pairwise_secret_encrypted_trustee_$i-$tid.xml
      rm ./pairwise_secret_trustee_$i-$tid.xml
   fi
   rm ./pairwise_secret_trustee_$tid-$i.xml

   i=`expr $i + 1`
done
echo "</PairwiseSecrets>" >> ./_pairwise_secrets_trustee_$tid.xml

# Generate committments from this trustee
echo -n "TRUSTEE $tid: generating committments ... "
vhti_call generate_commitment \
   ../transcript/config/key_gen_parameters.xml \
   ../transcript/config/trustee_$tid.xml \
   ../transcript/config/broadcast_values.xml \
   ./_pairwise_secrets_trustee_$tid.xml \
   ./secret_share_trustee_$tid.xml ./key_share_commitment_trustee_$tid.xml
mv ./key_share_commitment_trustee_$tid.xml ../transcript/config
echo "done."

# Check commitments from this trustee 
echo -n "TRUSTEE $tid: checking committments ... "
vhti_call check_commitment \
   ../transcript/config/key_gen_parameters.xml \
   ../transcript/config/trustee_$tid.xml \
   ../transcript/config/broadcast_values.xml \
   ../transcript/config/key_share_commitment_trustee_$tid.xml \
   ./_result.xml
if test "$(cat _result.xml)" != "<CheckResults>0:Success</CheckResults>" ; then
   echo -n "FAILED: "
   cat _result.xml
   exit 2
fi
echo "done."

# Create committed trustee
echo -n "TRUSTEE $tid: generating CommittedAuthority ... "
echo "<CommittedAuthority>" > ./committed_trustee_$tid.xml
cat ../transcript/config/trustee_$tid.xml >> ./committed_trustee_$tid.xml
echo '' >> ./committed_trustee_$tid.xml    # force a line-feed
cat ../transcript/config/key_share_commitment_trustee_$tid.xml >> ./committed_trustee_$tid.xml
echo '' >> ./committed_trustee_$tid.xml    # force a line-feed
echo "</CommittedAuthority>" >> ./committed_trustee_$tid.xml

mv ./committed_trustee_$tid.xml ../transcript/config
rm ../transcript/config/trustee_$tid.xml 
echo "done."

# Clean-up
rm -f ./_*
