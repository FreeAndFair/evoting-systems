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
   echo "Usage: trustee_gen_verification_stmts_1.sh TRUSTEE_ID ELECTION_ID PRECINCT_ID"
   exit 2
fi
tid=$1
eid=$2
pid=$3

# Generate pre vcode box and append to pre_verification_code_boxes.xml
echo "TRUSTEE $tid: generating pre verification code box ... "
vhti_call generate_pre_verification_results \
   ./vote_verification_key_trustee_$tid.xml \
   ../transcript/precinct_$eid-$pid/ballotbox/signed_voted_ballots.xml \
   ../transcript/precinct_$eid-$pid/config/blank_ballot_signed.xml \
   ../transcript/config/public_key_leo.xml \
   ./_pre_vcode_box.xml
perl ../perl/append_to.pl \
   ./_pre_vcode_box.xml \
   ../transcript/precinct_$eid-$pid/tabulation/trustee_pre_verification_code_boxes.xml \
   "PreVerificationCodeBoxes"
rm ./_pre_vcode_box.xml
echo "... done generating pre verification code box."

# Check "signed blank ballot" signature
echo -n "TRUSTEE $tid: checking signature on SignedBlankBallot ... "
vhti_call check_xml \
   ../transcript/config/public_key_leo.xml \
   ../transcript/precinct_$eid-$pid/config/blank_ballot_signed.xml \
   \"BlankBallot\" \
   ./_result.xml ./_bb.xml
if test "$(cat _result.xml)" != "<CheckResults>0:Success</CheckResults>" ; then
   echo -n "FAILED: "
   cat _result.xml
   exit 2
fi
echo "done."

# Generate codebook secrets and append to trustee_codebook_secrets_boxes.xml
echo "TRUSTEE $tid: generating codebook secrets for unused BSNs ... "

# Unused BSNs
perl ../perl/extract_element.pl ../transcript/config/committed_trustee_$tid.xml ./_trustee_$tid.xml "Authority"
vhti_call generate_dictionary_secrets \
   ../transcript/precinct_$eid-$pid/ballotbox/signed_voted_ballots.xml \
   ./_trustee_$tid.xml \
   ./private_key_keyshare_trustee_$tid.xml \
   ./vote_verification_key_trustee_$tid.xml \
   ./_bb.xml \
   ../transcript/precinct_$eid-$pid/tabulation/bsn_unused.xml \
   ../transcript/precinct_$eid-$pid/tabulation/revealed_codebook_secrets_trustee_$tid.xml
perl ../perl/append_to.pl \
   ../transcript/precinct_$eid-$pid/tabulation/revealed_codebook_secrets_trustee_$tid.xml \
   ../transcript/precinct_$eid-$pid/tabulation/trustee_revealed_codebook_secrets_box.xml \
   "TrusteeRevealedDictionarySecretsBox"

# Unused provisional BSNs
# BUGBUG: this fails if no provisional BSNs are defined (i.e., bsnp.xml is empty)
# TODO: support for generating codebooks for unused provisional BSNs
echo "... done generating codebook secrets for unused bsns."

# Clean-up
rmdir precinct_$eid-$pid  # BUGBUG: for some reason, unsnarf drops a directory
rmdir tabulation # BUGBUG: for some reason, unsnarf drops a directory
rmdir transcript  # BUGBUG: for some reason, unsnarf drops a directory
rm -f ./_*
