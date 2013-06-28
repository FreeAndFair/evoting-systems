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
if test $# -lt 1 ; then
   echo "Usage: audit_check_election_config.sh NUMBER_OF_TRUSTEES"
   exit 2
fi
n=$1

# Check commitments from trustees
../perl/cep2kgp.sh ../transcript/config/crypto_election_parameters.xml ./_key_gen_parameters.xml
i=1
while test $i -le $n ; do
   perl ../perl/extract_element.pl ../transcript/config/committed_trustee_$i.xml ./_trustee_$i.xml "Authority"
   perl ../perl/extract_element.pl ../transcript/config/committed_trustee_$i.xml ./_key_share_commitment_trustee_$i.xml "KeyShareCommitment"
   echo -n "AUDIT: checking TRUSTEE $i committments ... "
   vhti_call check_commitment \
      ./_key_gen_parameters.xml \
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


# Clean-up
rm -f ./_*