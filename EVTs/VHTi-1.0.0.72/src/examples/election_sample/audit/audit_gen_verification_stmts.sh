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
if test $# -lt 3 ; then
   echo "Usage: audit_gen_verification_stmts.sh VERIFICATION_CODE_BITS ELECTION_ID PRECINCT_ID"
   exit 2
fi
vcbitlen=$1
eid=$2
pid=$3
vcencoding="<AlphabetEncoding>HEX</AlphabetEncoding>"

# Regenerate verification statements from partially decrypted verification statements
echo -n "AUDIT: generating verification statements ... "
vhti_call check_vcode_partial_decrypts_and_combine \
   ../transcript/precinct_$eid-$pid/tabulation/trustee_pre_verification_code_boxes.xml \
   ../transcript/precinct_$eid-$pid/tabulation/trustee_partial_verification_stmts_decrypts.xml \
   ../transcript/precinct_$eid-$pid/ballotbox/signed_voted_ballots.xml \
   ../transcript/precinct_$eid-$pid/config/blank_ballot_signed.xml \
   ../transcript/config/public_key_leo.xml \
   $vcbitlen \
   $vcencoding \
   ./precinct_$eid-$pid/verification_statements.xml \
   ./_result.xml
if test "$(cat _result.xml)" != "<CheckResults>0:Success</CheckResults>" ; then
   echo -n "FAILED: "
   cat _result.xml
   exit 2
fi
echo "done."

# Compare these verification against those published by trustees
echo -n "AUDIT: comparing AUDIT and LEO verification statements ... "
declare -a _result=$(diff -q -b ../transcript/precinct_$eid-$pid/tabulation/verification_statements.xml ./precinct_$eid-$pid/verification_statements.xml)
if test "$_result" != "" ; then
   echo -n "FAILED."
   exit 2
fi
echo "done."

# Clean-up
rm -f ./_*