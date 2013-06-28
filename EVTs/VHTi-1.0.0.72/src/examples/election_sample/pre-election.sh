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

# Set-up environment
. ./env.sh

###################
# PRE-ELECTION TASKS FOR LEO AND TRUSTEES
# GIVEN
#   leo/ballots/bb_skeleton_$VHTI_ELECTION_SAMPLE_EID-$VHTI_ELECTION_SAMPLE_PID.xml
###################

# Usage
if test $# -lt 0 ; then
   echo "Usage: pre-election.sh [JUST_CLEAN]"
   echo "   JUST_CLEAN = 1 delete old election data and quit"
   exit 2
fi
clean=$1
if test -z $clean ; then
   clean=0
fi

echo -e  "\n"
echo     "====================================================================="
echo     "=============== PRE-ELECTION ========================================"
echo     "====================================================================="
echo -e  "\n"


echo     "=============== CLEANING UP OLD ELECTION DATA ======================="
rm -r -f ./transcript
rm -f ./leo/*.xml
rm -f ./dre/*.xml
rm -f -r ./trustee_*
rm -r -f ./dre/ballotbox*
rm -r -f ./observer_voter/precinct*
rm -r -f ./audit/precinct*
echo -e  "=============== CLEANING UP OF OLD ELECTION DATA COMPLETE ===========\n"
if test $clean -eq 1 ; then
   exit
fi

mkdir -p ./transcript/config
mkdir -p ./transcript/precinct_$VHTI_ELECTION_SAMPLE_EID-$VHTI_ELECTION_SAMPLE_PID
mkdir -p ./transcript/precinct_$VHTI_ELECTION_SAMPLE_EID-$VHTI_ELECTION_SAMPLE_PID/config
mkdir -p trustee_1
mkdir -p trustee_2
mkdir -p trustee_3

echo     "=============== LEO ELECTION INITIALIZATION ========================="
# LEO: Election initialization
# Description:
#  Generates initial random_state.xml
#  Generate cryptographic election parameters required for the election
cd leo
./leo_election_init.sh $VHTI_ELECTION_SAMPLE_N $VHTI_ELECTION_SAMPLE_T
./leo_gen_bsn.sh $VHTI_ELECTION_SAMPLE_EID $VHTI_ELECTION_SAMPLE_PID $VHTI_ELECTION_SAMPLE_NBSN $VHTI_ELECTION_SAMPLE_NBSNP
cd ..
echo -e  "=============== LEO ELECTION INITIALIZATION COMPLETE ================\n"


echo     "=============== TRUSTEE ELECTION INITIALIZATION ====================="
# TRUSTEE: Election initialization
# Description:
#  Run by every trustee to:
#     1. Generate initial random_state.xml
#     2. Generate their private (trustee_prvkey_#.xml) and public keys (../transcript/trustee_#.xml)
#     3. Generate broadcast values (broadcast_values_#.xml) for generating group election key.
# Precondition:
#  LEO initialized cryptographic election parameters
cd trustee_1
../trustee/trustee_election_init.sh 1
cd ..
echo ""

cd trustee_2
../trustee/trustee_election_init.sh 2
cd ..
echo ""

cd trustee_3
../trustee/trustee_election_init.sh 3
cd ..
echo -e  "=============== TRUSTEE ELECTION INITIALIZATION COMPLETE ============\n"


echo     "=============== TRUSTEE KEY SHARE PASS 1 ============================"
# TRUSTEE: Generate pairwise secrets
# Precondition:
#  All trustees have been created
cd trustee_1
../trustee/trustee_gen_pairwise_secrets.sh 1 $VHTI_ELECTION_SAMPLE_N
cd ..
echo ""

cd trustee_2
../trustee/trustee_gen_pairwise_secrets.sh 2 $VHTI_ELECTION_SAMPLE_N
cd ..
echo ""

cd trustee_3
../trustee/trustee_gen_pairwise_secrets.sh 3 $VHTI_ELECTION_SAMPLE_N
cd ..
echo -e  "=============== TRUSTEE KEY SHARE PASS 1 COMPLETE ===================\n"


echo     "=============== TRUSTEE KEY SHARE PASS 2 ============================"
# TRUSTEE: Generate keyshare commitments
# Precondition:
#  All trustees have generated broadcast values and pairwise secrets
cd trustee_1
../trustee/trustee_gen_keyshare_commitments.sh 1 $VHTI_ELECTION_SAMPLE_N
cd ..
echo ""

cd trustee_2
../trustee/trustee_gen_keyshare_commitments.sh 2 $VHTI_ELECTION_SAMPLE_N
cd ..
echo ""

cd trustee_3
../trustee/trustee_gen_keyshare_commitments.sh 3 $VHTI_ELECTION_SAMPLE_N
cd ..
echo -e  "=============== TRUSTEE KEY SHARE PASS 2 COMPLETE ===================\n"


echo     "=============== LEO POST-TRUSTEE KEY SHARE INITIALIZATION ==========="
cd leo
# LEO: Generate election public key
# Description:
#  Concatenate each trustees broadcast value into broadcast_values.xml
#  Create election public key
# Precondition:
#  All trustees have generated broadcast values
./leo_election_pubkey.sh $VHTI_ELECTION_SAMPLE_N

# LEO: Generate CryptoElectionParameters
# Precondition:
#  All trustees have generated commitments
./leo_gen_crypto_election_parameters.sh $VHTI_ELECTION_SAMPLE_N $VHTI_ELECTION_SAMPLE_T

# LEO: Generate BlankBallot
# Precondition:
#  CryptoElectionParameters have been generated
./leo_gen_blank_ballot.sh $VHTI_ELECTION_SAMPLE_EID $VHTI_ELECTION_SAMPLE_PID
cd ..
echo -e  "=============== LEO POST-TRUSTEE KEY SHARE INITIALIZATION COMPLETE ==\n"


echo     "=============== TRUSTEE CODEBOOK COMMIT ============================="
# TRUSTEE: Generate codebook commitments
# Precondition:
#  Blank ballot and BSNs generated
cd trustee_1
../trustee/trustee_gen_codebook_commitments.sh 1 $VHTI_ELECTION_SAMPLE_EID $VHTI_ELECTION_SAMPLE_PID
cd ..
echo ""

cd trustee_2
../trustee/trustee_gen_codebook_commitments.sh 2 $VHTI_ELECTION_SAMPLE_EID $VHTI_ELECTION_SAMPLE_PID
cd ..
echo ""

cd trustee_3
../trustee/trustee_gen_codebook_commitments.sh 3 $VHTI_ELECTION_SAMPLE_EID $VHTI_ELECTION_SAMPLE_PID
cd ..
echo -e  "=============== TRUSTEE CODEBOOK COMMIT COMPLETE ====================\n"


echo     "====================================================================="
echo     "=============== PRE-ELECTION COMPLETE! =============================="
echo     "====================================================================="
