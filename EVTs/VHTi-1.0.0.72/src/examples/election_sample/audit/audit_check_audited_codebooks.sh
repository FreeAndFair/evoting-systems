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
   echo "Usage: audit_check_audited_codebooks.sh ELECTION_ID PRECINCT_ID"
   exit 2
fi
eid=$1
pid=$2

# How many codebooks were audited?
declare -a codebooks=($(ls ../observer_voter/precinct_$eid-$pid/*-cb.xml))
ncodebooks=${#codebooks[@]}
if test $ncodebooks == 0 ; then
   echo No codebooks to audit
   exit
fi

# Check poll-site audited codebook against revealed codebooks
nfailed=0
i=0
while test $i -lt $ncodebooks ; do
   echo "AUDIT: auditing ${codebooks[$i]} ... "

   perl ../perl/extract_element.pl ${codebooks[$i]} ./_bsn.xml "BallotSequenceNumber"
   perl ./audit_get_codebook.pl ./precinct_$eid-$pid/trustee_revealed_codebooks.xml ./_bsn.xml ./_cb.xml

   declare -a _result=$(diff -q -b ${codebooks[$i]} ./_cb.xml)
   if test "$_result" != "" ; then
      nfailed=`expr $nfailed + 1`
      declare bsn=$(cat ./_bsn.xml)
      echo "ERROR: codebook audit failed for $bsn."
   fi
   echo "... done codebook audit."
   echo ""

   i=`expr $i + 1`
done

if test $nfailed -gt 0 ; then
   echo "AUDIT: $nfailed of $ncodebooks codebook audits failed"
fi

# Clean-up
rm -f ./_*