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

#include <vhti/types.h>
#include <support_test/test-data.h>
#include <test_misc/test-misc.h>

// These are all well-formed, but invalid.
const char *const invalid_authority = "<" VOTER_ROLL" />";
const char *const invalid_random_state = "<" BROADCAST_VALUES " />";
const char *const invalid_cg_parameters = "<" BROADCAST_VALUES " />";
const char *const invalid_election_id = "<" BROADCAST_VALUES " />";
const char *const invalid_precinct_id = "<" BROADCAST_VALUES " />";
const char *const invalid_ballot_questions = "<" BROADCAST_VALUES " />";
const char *const invalid_display_info = "<" BROADCAST_VALUES " />";
const char *const invalid_key_gen_parameters = "<" BROADCAST_VALUES " />";
const char *const invalid_encoding = "<" BROADCAST_VALUES " />";
const char *const invalid_ce_parameters = "<" BROADCAST_VALUES " />";
const char *const invalid_bb = "<" VOTER_ROLL " />";
const char *const invalid_bsns = "<" VOTER_ROLL" />";
const char *const invalid_prvkey = "<" VOTER_ROLL" />";
const char *const invalid_vkey = "<" VOTER_ROLL" />";
const char *const invalid_ballot_skeleton = "<" VOTER_ROLL" />";

const char * valid_authority;

const char *const valid_random_state =
"<RandomState SourceType=\"PSEUDO FROM HASH\">"
"<RandomSeedKey>"
"Some kind of random data to hash"
"</RandomSeedKey>"
"<RandomBlock Encoding=\"DEC\">"
"1080159859926833460887638203863366617559462040602"
"</RandomBlock>"
"</RandomState>";

const char * valid_cg_parameters;

const char *const valid_election_id =
"<ElectionID>21740</ElectionID>";

const char *const valid_precinct_id =
"<PrecinctID>99</PrecinctID>";

const char *const valid_display_info =
"<BallotTextStructure>Describes the layout of the ballot.</BallotTextStructure>";

const char * valid_key_gen_parameters;
const char *const valid_encoding =
"<AlphabetEncoding>DEC</AlphabetEncoding>";

const char *valid_ce_parameters;

const char * valid_bb;

const char * valid_prvkey ;

const char *const valid_vkey =
"<VoteVerificationKey>This here is my special key</VoteVerificationKey>";

const char *const valid_bsns =
"<BallotSequenceNumbers>"
"<BallotSequenceNumber Encoding=\"DEC\">18</BallotSequenceNumber>"
"</BallotSequenceNumbers>";

const char * valid_ballot_skeleton;

void
initialize_data ()
{
   const char data_root[] = "../../vhti/bindings/perl/examples/";

   valid_authority              = snarf (data_root, "auth0.xml");
   valid_cg_parameters          = snarf (data_root, "cgp.xml");
   valid_key_gen_parameters     = snarf (data_root, "kgp.xml");
   valid_ce_parameters          = snarf (data_root, "cep.xml");
   valid_bb                     = snarf (data_root, "bb.xml");
   valid_prvkey                 = snarf (data_root, "auth0/private-key");
   valid_ballot_skeleton        = snarf (data_root, "ballot-skeleton.xml");
}
