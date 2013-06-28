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
   echo "Usage: leo_election_init.sh NUMBER_OF_TRUSTEES THRESHOLD"
   exit 2
fi
n=$1
t=$2

# Generate random seed key
# WARNING: For demonstration purposes, we use a random seed from the shell 
# command "times" which is certainly NOT cryptographically secure. 
# Cryptographically secure random seeds are the responsibility of the 
# VHTi-integrated voting application.
echo "<RandomSeedKey>" > ./_random_seed_key.xml
times >> ./_random_seed_key.xml
echo $n >> ./_random_seed_key.xml
echo "</RandomSeedKey>" >> ./_random_seed_key.xml

# Generate initial random state
echo -n "LEO: generating random state ... "
vhti_call generate_random_state \
   ./_random_seed_key.xml \
   ./random_state.xml
echo "done."

# Generate SeedParameters
echo "<SeedParameters>" > ./_seed_parameters.xml
echo "<NumAuth>$n</NumAuth>" >> ./_seed_parameters.xml
echo "<Threshold>$t</Threshold>" >> ./_seed_parameters.xml
echo "</SeedParameters>" >> ./_seed_parameters.xml

# Create LEO general purpose key-pair
echo -n "LEO: generating LEO general purpose key-pair ... "
vhti_call generate_keys \
   "<IdentInfo>LEO</IdentInfo>" \
   ./private_key_leo.xml ./public_key_leo.xml
mv ./public_key_leo.xml ../transcript/config
echo "done."

# Create DRE general purpose key-pair 
echo -n "LEO: generating DRE general purpose key-pair ... "
vhti_call generate_keys \
   "<IdentInfo>DRE</IdentInfo>" \
   ./private_key_dre.xml ./public_key_dre.xml
mv ./public_key_dre.xml ../transcript/config
echo "done."

# Generate key generation parameters
echo -n "LEO: generating key generation parameters ... "
vhti_call create_keygen_parameters \
   ./_seed_parameters.xml \
   ./random_state.xml \
   ../transcript/config/key_gen_parameters.xml ./random_state.xml
echo "done."
perl leo_kgp2cgp.pl ../transcript/config/key_gen_parameters.xml ../transcript/config/crypto_group_parameters.xml
rmdir config  # BUGBUG: for some reason, unsnarf drops a directory
rmdir transcript  # BUGBUG: for some reason, unsnarf drops a directory

# Clean-up
rm -f ./_*
