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
   echo "Usage: trustee_gen_pairwise_secrets.sh TRUSTEE_ID NUMBER_OF_TRUSTEES"
   exit 2
fi
tid=$1
n=$2

# Generate pairwise secret from this trustee to other trustees
echo "TRUSTEE $tid: generating secrets ... "
i=1
while test $i -le $n; do
   echo "   ... to TRUSTEE $i ... "
   vhti_call generate_secret \
      ../transcript/config/key_gen_parameters.xml \
      ../transcript/config/trustee_$i.xml \
      ./secret_coefficients_trustee_$tid.xml \
      ./pairwise_secret_trustee_$tid-$i.xml

   # Send this pairwise secret to trustee $i
   # WARNING: this is a secret between TRUSTEE $tid and TRUSTEE $i 
   # and secure (i.e., encrypted) transmission is used
   if test $i -ne $tid ; then
      echo -n "       encrypting pairwise_secret_trustee_$tid-$i.xml and sending to TRUSTEE $i ... "
      vhti_call encrypt \
         ../transcript/config/public_key_trustee_$i.xml \
         ./pairwise_secret_trustee_$tid-$i.xml \
         ./pairwise_secret_encrypted_trustee_$tid-$i.xml
      mv ./pairwise_secret_encrypted_trustee_$tid-$i.xml ../trustee_$i 
      echo "done." 
   fi

   i=`expr $i + 1`
done
echo "   ... done."

# Remove redundant data
rm ./secret_coefficients_trustee_$tid.xml

# Clean-up
rm -f ./_*
