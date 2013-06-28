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
   echo "Usage: trustee_gen_verification_stmts_2.sh TRUSTEE_ID ELECTION_ID PRECINCT_ID"
   exit 2
fi
tid=$1
eid=$2
pid=$3

# Generate partial verification results
echo "TRUSTEE $tid: generating partial verification results ... "
vhti_call generate_partial_verification_results \
   ../transcript/precinct_$eid-$pid/tabulation/trustee_pre_verification_code_boxes.xml \
   ../transcript/precinct_$eid-$pid/config/blank_ballot_signed.xml \
   ../transcript/config/public_key_leo.xml \
   ../transcript/config/committed_trustee_$tid.xml \
   ./secret_share_trustee_$tid.xml \
   ./random_state.xml \
   ./_apdv.xml ./random_state.xml
perl ../perl/append_to.pl \
   ./_apdv.xml \
   ../transcript/precinct_$eid-$pid/tabulation/trustee_partial_verification_stmts_decrypts.xml \
   "AuthorityPartialDecrypts"
rm ./_apdv.xml
rmdir transcript  # BUGBUG: for some reason, unsnarf drops a directory
rmdir precinct_$eid-$pid # BUGBUG: for some reason, unsnarf drops a directory
rmdir tabulation  # BUGBUG: for some reason, unsnarf drops a directory
echo "... done generating partial verification results."

# Clean-up
rm -f ./_*
