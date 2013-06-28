/*  */
/* This material is subject to the VoteHere Source Code Evaluation */
/* License Agreement ("Agreement").  Possession and/or use of this */
/* material indicates your acceptance of this Agreement in its entirety. */
/* Copies of the Agreement may be found at www.votehere.net. */
/*  */
/* Copyright 2004 VoteHere, Inc.  All Rights Reserved */
/*  */
/* You may not download this Software if you are located in any country */
/* (or are a national of a country) subject to a general U.S. or */
/* U.N. embargo or are deemed to be a terrorist country (i.e., Cuba, */
/* Iran, Iraq, Libya, North Korea, Sudan and Syria) by the United States */
/* (each a "Prohibited Country") or are otherwise denied export */
/* privileges from the United States or Canada ("Denied Person"). */
/* Further, you may not transfer or re-export the Software to any such */
/* country or Denied Person without a license or authorization from the */
/* U.S. government.  By downloading the Software, you represent and */
/* warrant that you are not a Denied Person, are not located in or a */
/* national of a Prohibited Country, and will not export or re-export to */
/* any Prohibited Country or Denied Party. */
// Copyright 2003 VoteHere Inc. All Rights Reserved.

#include "vhti/types.h"
#include "support_test/test-data.h"
#include <test_misc/test-misc.h>

// These are all well-formed, but invalid.
const char *const invalid_answer_ref = "<" VOTER_ROLL" />";
const char *const invalid_authority = "<" VOTER_ROLL" />";
const char *const invalid_ballot_secrets = "<" VOTER_ROLL" />";
const char *const invalid_bb = "<" VOTER_ROLL " />";
const char *const invalid_bsn = "<" VOTER_ROLL" />";
const char *const invalid_bsns = "<" VOTER_ROLL" />";
const char *const invalid_ce_parameters = "<" VOTER_ROLL " />";
const char *const invalid_cert  = "<" VOTER_ROLL " />";
const char *const invalid_clear_text_ballot  = "<" VOTER_ROLL " />";
const char *const invalid_election_id = "<" VOTER_ROLL" />";
const char *const invalid_election_node = "<" VOTER_ROLL" />";
const char *const invalid_encoding = "<" VOTER_ROLL" />";
const char *const invalid_precinct_id = "<" VOTER_ROLL" />";
const char *const invalid_prng = "<" VOTER_ROLL " />";
const char *const invalid_prvkey = "<" VOTER_ROLL" />";
const char *const invalid_pubkey = "<" VOTER_ROLL" />";
const char *const invalid_random_seed_key = "<" VOTER_ROLL" />";
const char *const invalid_random_state = "<" VOTER_ROLL" />";
const char *const invalid_sbb  = "<" VOTER_ROLL " />";
const char *const invalid_signature = "<" VOTER_ROLL" />";
const char *const invalid_signed_status_query_struct = "<" VOTER_ROLL" />";
const char *const invalid_sigpub  = "<" VOTER_ROLL " />";
const char *const invalid_svb = "<" VOTER_ROLL " />";
const char *const invalid_vkey = "<" VOTER_ROLL" />";
const char *const invalid_vkeys = "<" VOTER_ROLL" />";
const char *const invalid_vote_receipt = "<" VOTER_ROLL" />";
const char *const invalid_vote_receipt_data = "<" VOTER_ROLL" />";
const char *const invalid_voted_answer = "<" VOTER_ROLL" />";
const char *const invalid_vr  = "<" BLANK_BALLOT "> Hey you!!</" BLANK_BALLOT ">";
const char *const invalid_vv_ballot = "<" VOTER_ROLL " />";

const char *const not_xml = "This isn't even well-formed XML, let alone valid.";

const char * valid_authority;

const char * valid_svb;

const char * valid_bb;

const char * valid_rbb ;

const char *const invalid_rbb =
"<RawBallotBox>"
"<Flugelhorn />"
"</RawBallotBox>";

const char * valid_sbb;

const char * const valid_cert ="<Certificate>"
"<GeneralPurposePublicKey>"
"<IdentInfo>You guessed it -- nobody pays any attention to me</IdentInfo>"
"<SigningPublicKey/>"
"<EncryptionPublicKey/>"
"</GeneralPurposePublicKey>"
"</Certificate>";

const char * valid_sigpub ;

const char * valid_clear_text_ballot;

const char *const valid_vv_ballot =
"<ValidatedVotedBallot>"
"I think we need a better dtd definition for this."
"</ValidatedVotedBallot>";

const char * valid_ce_parameters;

const char *const valid_ballot_secrets = "<BallotSecrets><BallotSecret Encoding=\"BOB\">Yet another ignored element</BallotSecret></BallotSecrets>";

const char * valid_vote_receipt;

const char *const valid_election_id =
"<ElectionID>"
"21740"
"</ElectionID>";

const char *const valid_precinct_id =
"<PrecinctID>"
"99"
"</PrecinctID>";

const char *const valid_signature =
"<Signature>MC0CFFv0t5tGCS8CeBmQDxlK96Wq2Ze/AhUAwf8qhj2Kz+UYnNRdDQHecGQorEs=</Signature>";

const char *const valid_election_node =
"<ElectionNode>"
"node"
"</ElectionNode>";

const char *const valid_random_seed_key =
"<RandomSeedKey>"
"Yo momma wears Army boots"
"</RandomSeedKey>";

const char *const valid_voted_answer =
"<VotedAnswer/>";

const char *const valid_random_state =
"<RandomState SourceType=\"PSEUDO FROM HASH\">"
"<RandomSeedKey>"
"Some kind of random data to hash"
"</RandomSeedKey>"
"<RandomBlock Encoding=\"DEC\">"
"1080159859926833460887638203863366617559462040602"
"</RandomBlock>"
"</RandomState>";

const char * valid_prvkey;
const char * valid_pubkey;

const char *const valid_vkey =
"<VoteVerificationKey>This here is my special key</VoteVerificationKey>";

const char *const valid_vkeys =
"<VoteVerificationKeys>"
"<VoteVerificationKey>This here is my special key</VoteVerificationKey>"
"</VoteVerificationKeys>";

const char *const valid_bsn =
"<BallotSequenceNumber Encoding=\"DEC\">1</BallotSequenceNumber>";

const char *const valid_bsns =
"<BallotSequenceNumbers>"
"<BallotSequenceNumber Encoding=\"DEC\">18</BallotSequenceNumber>"
"</BallotSequenceNumbers>";

/* This text has to conform to that generated by VHTI_generate_blank_ballot */
const char *const valid_answer_ref = "<AnswerReference>A0</AnswerReference>";

const char * valid_vote_receipt_data;

const char *const valid_encoding =
"<AlphabetEncoding>DEC</AlphabetEncoding>";

void
initialize_data ()
{
   const char data_root[] = "../../vhti/bindings/perl/examples/";

   valid_authority              = snarf (data_root, "auth0.xml");
   valid_bb                     = snarf (data_root, "bb.xml");
   valid_sbb                    = snarf (data_root, "sbb.xml");
   valid_sigpub                 = snarf (data_root, "pollsite-pubkey.xml");
   valid_ce_parameters          = snarf (data_root, "cep.xml");
   valid_prvkey                 = snarf (data_root, "pollsite-private-key.xml");
   valid_pubkey                 = snarf (data_root, "pollsite-pubkey.xml");
   valid_svb                    = snarf (data_root, "voter-Joe_Voter_#0/svb.xml");
   valid_clear_text_ballot      = snarf (data_root, "voter-Joe_Voter_#0/ctb.xml");
   valid_vote_receipt           = snarf (data_root, "voter-Joe_Voter_#0/receipt.xml");
   valid_vote_receipt_data      = snarf (data_root, "voter-Joe_Voter_#0/receipt-data.xml");
   valid_rbb                    = snarf (data_root, "rbb.xml");
}
