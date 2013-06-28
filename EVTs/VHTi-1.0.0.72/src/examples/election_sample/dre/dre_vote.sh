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
   echo "Usage: dre_vote.sh CODE_BIT_LENGTH ELECTION_ID PRECINCT_ID [CODEBOOK_ONLY] [CHEAT]"
   echo "   CODEBOOK_ONLY = 1 just generate a codebook and quit"
   echo "   CHEAT may be:"
   echo "      1  Change ballot before voter leaves polling place"
   echo "      2  Change ballot after voter leaves polling place"
   exit 2
fi

vcencoding="<AlphabetEncoding>HEX</AlphabetEncoding>"
vcbitlen=$1
eid=$2
pid=$3
cb_only=$4
cheat=$5
if test -z $cb_only ; then
   cb_only=0
fi
if test -z $cheat ; then
   cheat=0
fi

# Check the blank ballot signature in SignedBlankBallot
echo -n "DRE: checking SignedBlankBallot signature ... "
vhti_call check_xml \
   ./public_key_leo.xml \
   ./blank_ballot_signed.xml \
   \"BlankBallot\" \
   ./_result.xml ./_bb.xml
if test "$(cat _result.xml)" != "<CheckResults>0:Success</CheckResults>" ; then
   echo -n "FAILED: "
   cat _result.xml
   rm -f ./_*
   exit 2
fi
echo "done."

# Get the next BSN
perl dre_get_next_bsn.pl $eid $pid _bsnx.xml _bsn.xml
read bsn <_bsn.xml
if test $bsn = "-1" ; then
   echo "ERROR: No more BSNs to vote"
   exit 2
fi
echo "Voting ballot BSN #$bsn"

# Generate and commit codebook
echo -n "DRE: generating codebook ... "
vhti_call generate_vote_verification_dictionary \
   ./vote_verification_keys.xml \
   ./_bb.xml \
   ./_bsnx.xml \
   $vcbitlen \
   $vcencoding \
   ../observer_voter/precinct_$eid-$pid/$bsn-cb.xml
echo "done."
if test $cb_only -eq 1 ; then
   rm -f ./_*
   exit 0
fi

# Generate a random clear-text ballot (i.e., simulate a voter)
# This captures what the voter intended
echo "DRE: generating clear text ballot ... "
perl dre_gen_clear_text_ballot.pl _bb.xml _ctb.xml
cp _ctb.xml ./ballotbox_$eid-$pid/$bsn-ctb.xml  # what the voter intended
echo "... done generating clear text ballot."

# Cheat: change the ballot and show the wrong receipt
if test $cheat -eq 1 ; then
   echo "CHEATING: changing ballot before voter leaves polling place."
   perl dre_gen_clear_text_ballot.pl _bb.xml _ctb.xml    # cheated ballot, don't update results_expected file 
fi

# Encrypt and sign ballot
# NOTE: we're using the DRE key to sign. A key-pair given to the voter and 
# signed by the poll-worker could also be used if traceability to the 
# poll-worker is desirable
echo -n "DRE: encrypting and signing ballot ... "
vhti_call encrypt_ballot_pollsite \
   ./_ctb.xml \
   ./_bb.xml \
   ./_bsnx.xml \
   ./random_state.xml \
   ./private_key_dre.xml \
   ./_svb.xml ./random_state.xml
echo "done."

# Generate vote receipt
echo -n "DRE: generating vote receipt data ... "
vhti_call generate_vote_receipt_data \
   ./_svb.xml \
   ./vote_verification_keys.xml \
   ./_bb.xml \
   ./_bsnx.xml \
   ./_ctb.xml \
   $vcbitlen \
   $vcencoding \
   ./_vrd.xml
echo "done."

# Add BSN to raw vote receipt to facilitate easy look up
# with the verification statment at tabulation time
cp ./_vrd.xml ../observer_voter/precinct_$eid-$pid/$bsn-vr.xml

# Observer/voter checks vote receipt against their intent
echo "OBSERVER/VOTER: checking vote receipt against voter intent ... "
perl ../observer_voter/observer_check_receipt.pl \
   ./ballotbox_$eid-$pid/$bsn-ctb.xml \
   ../observer_voter/precinct_$eid-$pid/$bsn-cb.xml \
   ../observer_voter/precinct_$eid-$pid/$bsn-vr.xml \
   ./_result.xml
if test "$(cat _result.xml)" != "<CheckResults>0:Success</CheckResults>" ; then
   # Since an error was caught, and ballot not cast, don't save the SignedVotedBallot
   cat _result.xml
   echo ""
   echo "ERROR: voter not casting this ballot since vote receipt doesn't match."
   mv ./ballotbox_$eid-$pid/$bsn-ctb.xml ../observer_voter/precinct_$eid-$pid/$bsn-ctb-challenged.xml  # what the voter intended
   mv ../observer_voter/precinct_$eid-$pid/$bsn-cb.xml ../observer_voter/precinct_$eid-$pid/$bsn-cb-challenged.xml 
   mv ../observer_voter/precinct_$eid-$pid/$bsn-vr.xml ../observer_voter/precinct_$eid-$pid/$bsn-vr-challenged.xml
   rm -f ./_*
   exit 2
fi
echo "... done checking vote receipt against voter intent."

# Commit the vote
cp _svb.xml ./ballotbox_$eid-$pid/$bsn-svb.xml
rm ../observer_voter/precinct_$eid-$pid/$bsn-cb.xml   # for voter privacy, destroy codebook
perl dre_update_expected_results.pl _bb.xml _ctb.xml ./ballotbox_$eid-$pid/results_expected.xml

# Sign and commit vote receipt
echo -n "DRE: signing vote receipt data ... "
vhti_call sign_receipt \
   ./_vrd.xml \
   ./private_key_dre.xml \
   ../observer_voter/precinct_$eid-$pid/$bsn-vrs.xml
echo "done."

# Observer/Voter checks vote receipt against voted ballot
echo -n "OBSERVER/VOTER: checking vote receipt signature ... "
vhti_call check_xml \
   ../transcript/config/public_key_dre.xml \
   ../observer_voter/precinct_$eid-$pid/$bsn-vrs.xml \
   \"VoteReceiptData\" \
   ./_result.xml ./_vr.xml
if test "$(cat _result.xml)" != "<CheckResults>0:Success</CheckResults>" ; then
   echo -n "FAILED: "
   cat _result.xml
   rm -f ./_*
   exit 2
fi
echo "done."

# Cheat: change the ballot after the voter leaves the polling place by showing the right receipt
if test $cheat -eq 2 ; then
   echo "CHEATING: changing ballot after voter leaves polling place."
   perl dre_gen_clear_text_ballot.pl _bb.xml _ctb.xml
   vhti_call encrypt_ballot_pollsite \
      ./_ctb.xml \
      ./_bb.xml \
      ./_bsnx.xml \
      ./random_state.xml \
      ./private_key_dre.xml \
      ./ballotbox_$eid-$pid/$bsn-svb.xml ./random_state.xml
fi

# Clean-up
rm -f ./_*
