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
   echo "Usage: trustee_election_init.sh TRUSTEE_ID"
   exit 2
fi
tid=$1

# Generate random seed key
# WARNING: For demonstration purposes, we use a random seed from the shell 
# command "times" which is certainly NOT cryptographically secure. 
# Cryptographically secure random seeds are the responsibility of the 
# VHTi-integrated voting application.
echo "<RandomSeedKey>" > ./_random_seed_key.xml
times >> ./_random_seed_key.xml
echo $tid >> ./_random_seed_key.xml
echo "</RandomSeedKey>" >> ./_random_seed_key.xml

# Generate initial random state
echo -n "TRUSTEE $tid: generating random state ... "
vhti_call generate_random_state \
   ./_random_seed_key.xml \
   ./random_state.xml
echo "done."

# Create trustee
echo -n "TRUSTEE $tid: creating trustee ... "
vhti_call create_authority \"Trustee_$tid\" \
   ../transcript/config/key_gen_parameters.xml \
   ./random_state.xml \
   \"\" \
   ./private_key_keyshare_trustee_$tid.xml ./trustee_$tid.xml ./random_state.xml
mv ./trustee_$tid.xml ../transcript/config
echo "done."

# Create trustee general purpose key-pair
echo -n "TRUSTEE $tid: generating general purpose key-pair ... "
vhti_call generate_keys \
   "<IdentInfo>Trustee $tid</IdentInfo>" \
   ./private_key_trustee_$tid.xml ./public_key_trustee_$tid.xml
mv ./public_key_trustee_$tid.xml ../transcript/config
echo "done."

# Generate vote verification key
# WARNING: the vote verification keys are sensitive
#  We give our vote verification key to the LEO for loading onto the DRE. It would
#  better (for voter privacy) to have the Trustee load it onto the DRE directly.
echo -n "TRUSTEE $tid: generating vote verification key share ... "
vhti_call generate_vvk \
   ./random_state.xml \
   ./vote_verification_key_trustee_$tid.xml ./random_state.xml 
cp ./vote_verification_key_trustee_$tid.xml ../leo  
echo "done."

# Generate secret coefficient
echo -n "TRUSTEE $tid: generating secret coefficients ... "
vhti_call generate_secret_coefficients \
   ../transcript/config/key_gen_parameters.xml \
   ../transcript/config/trustee_$tid.xml \
   ./random_state.xml \
   ./secret_coefficients_trustee_$tid.xml ./random_state.xml
echo "done."

# Generate broadcast value and append to ../transcript/config/broadcast_values.xml
echo -n "TRUSTEE $tid: generating broadcast value ... "
vhti_call generate_broadcast \
   ../transcript/config/key_gen_parameters.xml \
   ./secret_coefficients_trustee_$tid.xml \
   ./random_state.xml \
   ./_broadcast_value.xml ./random_state.xml
echo "done."
perl ../perl/append_to.pl ./_broadcast_value.xml ../transcript/config/broadcast_values.xml "BroadcastValues"
rm ./_broadcast_value.xml
rmdir transcript  # BUGBUG: for some reason, unsnarf drops a directory
rmdir config # BUGBUG: for some reason, unsnarf drops a directory

# Clean-up
rm -f ./_*
