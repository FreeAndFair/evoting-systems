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
# ELECTION
###################

# Usage
if test $# -lt 1 ; then
   echo "Usage: election.sh VOTES_TO_CAST [CHEAT] [JUST_CLEAN]"
   echo "   CHEAT may be:"
   echo "      1  Change ballot before voter leaves polling place"
   echo "      2  Change ballot after voter leaves polling place"
   echo "   JUST_CLEAN = 1 delete old election data and quit"
   exit 2
fi
nvotes=$1    # number of votes to cast
cheat=$2
if test -z $cheat ; then
   cheat=0
fi
clean=$3
if test -z $clean ; then
   clean=0
fi

echo -e  "\n"
echo     "====================================================================="
echo     "=============== VOTING =============================================="
echo     "====================================================================="
echo -e  "\n"


echo     "=============== CLEANING UP OLD ELECTION DATA ======================="
rm -f ./dre/*.xml
rm -f -r ./dre/ballotbox*
rm -f -r ./observer_voter/precinct*
echo -e  "=============== CLEANING UP OF OLD ELECTION DATA COMPLETE ===========\n"
if test $clean -eq 1 ; then
   exit
fi


echo -e  "=============== LEO LOADING DRE ====================================="
cd leo
./leo_load_dre.sh $VHTI_ELECTION_SAMPLE_EID $VHTI_ELECTION_SAMPLE_PID
cd ..
echo -e  "=============== LEO LOADING DRE COMPLETE ============================\n"


echo -e  "=============== DRE INITIALIZATION =================================="
cd dre
./dre_init.sh
cd ..
echo -e  "=============== DRE INITIALIZATION COMPLETE =========================\n"


echo -e  "=============== DRE VOTING =========================================="
cd dre
i=1
while test $i -le $nvotes ; do
   echo "VOTER $i ..."
   ./dre_vote.sh $VHTI_ELECTION_SAMPLE_VCBITS $VHTI_ELECTION_SAMPLE_EID $VHTI_ELECTION_SAMPLE_PID $cheat
   echo "... VOTER $i COMPLETE"
   i=`expr $i + 1`
   echo ""
done

ncb=`expr $nvotes / 3`
i=1
while test $i -le $ncb ; do
   echo "GENERATING CODEBOOK $i FOR AUDIT ..."
   ./dre_vote.sh $VHTI_ELECTION_SAMPLE_VCBITS $VHTI_ELECTION_SAMPLE_EID $VHTI_ELECTION_SAMPLE_PID 1
   echo "... CODEBOOK $i GENERATED"
   i=`expr $i + 1`
   echo ""
done

cd ..
echo -e  "=============== DRE VOTING COMPLETE =================================\n"


echo     "====================================================================="
echo     "=============== VOTING COMPLETE! ===================================="
echo     "====================================================================="
