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
# POST-ELECTION AUDIT
###################

# Usage
if test $# -lt 0 ; then
   echo "Usage: post-election-audit.sh [JUST_CLEAN]"
   echo "   JUST_CLEAN = 1 delete old election data and quit"
   exit 2
fi
clean=$1
if test -z $clean ; then
   clean=0
fi

echo -e  "\n"
echo     "====================================================================="
echo     "=============== POST-ELECTION AUDIT ================================="
echo     "====================================================================="
echo -e  "\n"


echo     "=============== CLEANING UP OLD AUDIT DATA =========================="
rm -f -r ./audit/precinct_$VHTI_ELECTION_SAMPLE_EID-$VHTI_ELECTION_SAMPLE_PID*
echo -e  "=============== CLEANING UP OF OLD AUDIT COMPLETE ===================\n"
if test $clean -eq 1 ; then
   exit
fi

mkdir -p ./audit/precinct_$VHTI_ELECTION_SAMPLE_EID-$VHTI_ELECTION_SAMPLE_PID

echo -e  "=============== CHECK RECEIPTS AGAINST VERIFICATION STMTS ==========="
cd observer_voter
./observer_check_verification_stmt.sh $VHTI_ELECTION_SAMPLE_EID $VHTI_ELECTION_SAMPLE_PID
cd ..
echo -e  "=============== RECEIPTS CHECK COMPLETE =============================\n"

echo -e  "=============== ELECTION AUDIT ======================================"
cd audit
./audit_check_election_config.sh $VHTI_ELECTION_SAMPLE_N
./audit_check_results.sh $VHTI_ELECTION_SAMPLE_EID $VHTI_ELECTION_SAMPLE_PID
./audit_gen_verification_stmts.sh $VHTI_ELECTION_SAMPLE_VCBITS $VHTI_ELECTION_SAMPLE_EID $VHTI_ELECTION_SAMPLE_PID
./audit_gen_revealed_codebooks.sh $VHTI_ELECTION_SAMPLE_N $VHTI_ELECTION_SAMPLE_VCBITS $VHTI_ELECTION_SAMPLE_EID $VHTI_ELECTION_SAMPLE_PID
./audit_check_audited_codebooks.sh $VHTI_ELECTION_SAMPLE_EID $VHTI_ELECTION_SAMPLE_PID
cd ..
echo -e  "=============== ELECTION AUDIT COMPLETE =============================\n"


echo     "====================================================================="
echo     "=============== POST-ELECTION AUDIT COMPLETE! ======================="
echo     "====================================================================="
