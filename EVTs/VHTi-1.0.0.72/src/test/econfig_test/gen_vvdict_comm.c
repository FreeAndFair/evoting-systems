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

#include "econfig_test.h"
#include "vhti/gen_vvdict_comm.h"
#include <stdio.h>
#include <malloc.h>
#include <support_test/test-data.h>

static void
expect_gen_vvdict_commits (CuTest *tc,
                      const int expected_status,
                      Authority authority,
                      GeneralPurposePrivateKey private_signature_key,
                      VoteVerificationKey prn_seed,
                      BlankBallot blank_ballot,
                      BallotSequenceNumbers bsns)
{
   char * trustee_dict_comm = 0;

   CuAssert (tc,
             (0 == expected_status ?
              "VHTI_generate_vcdict_commits should have accepted valid input"
              : "VHTI_generate_vcdict_commits should have rejected invalid input"),
             expected_status
             == VHTI_generate_vvdict_commits (authority, private_signature_key, prn_seed,
             blank_ballot, bsns, &trustee_dict_comm));

   if (0 != expected_status)
   {
      if (trustee_dict_comm)
         fprintf (stderr, "Hmm: `%s'\n", trustee_dict_comm);
      CuAssertPtrEquals (tc, NULL, trustee_dict_comm);
   }
   else
   {
      CuAssertPtrNotNull (tc, trustee_dict_comm);
      CuAssert (tc,
                "VHTI_generate_vcdict_commits should have returned a Trustee Dictionary Commitments.",
                0 == VHTI_validate (SIGNED_TRUSTEE_DICTIONARY_COMMITMENTS, trustee_dict_comm) );
      VHTI_free (trustee_dict_comm);
   }
}

void
gen_vvdict_commits_validation (CuTest *tc)
{
   expect_gen_vvdict_commits (tc, 0, valid_authority, valid_prvkey, valid_vkey, valid_bb, valid_bsns);
   expect_gen_vvdict_commits (tc, -1, invalid_authority, valid_prvkey, valid_vkey, valid_bb, valid_bsns);
   expect_gen_vvdict_commits (tc, -1, valid_authority, invalid_prvkey, valid_vkey, valid_bb, valid_bsns);
   expect_gen_vvdict_commits (tc, -1, valid_authority, valid_prvkey, invalid_vkey, valid_bb, valid_bsns);
   expect_gen_vvdict_commits (tc, -1, valid_authority, valid_prvkey, valid_vkey, invalid_bb, valid_bsns);
   expect_gen_vvdict_commits (tc, -1, valid_authority, valid_prvkey, valid_vkey, valid_bb, invalid_bsns);
}
