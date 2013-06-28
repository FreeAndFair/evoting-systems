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

#include "keyshare_test.h"
#include <vhti/check_comm.h>
#include <stdio.h>
#include <malloc.h>
#include <support_test/test-data.h>

static void
expect_check_commitment (CuTest *tc,
                          const int expected_status,
                          KeyGenParameters const key_gen_parameters,
                          Authority const authority,
                          BroadcastValues const broadcast_values,
                          KeyShareCommitment const keyshare_commitment)
{
   char *check_comm_results = 0;

   CuAssert (tc,
             (0 == expected_status ?
              "VHTI_check_commitment should have accepted valid input"
              : "VHTI_check_commitment should have rejected invalid input"),
             expected_status == VHTI_check_commitment (key_gen_parameters, authority,
             broadcast_values, keyshare_commitment, &check_comm_results));

   if (0 != expected_status)
   {
       if (check_comm_results)
         fprintf (stderr, "Hmm: `%s'\n", check_comm_results);
      CuAssertPtrEquals (tc, NULL, check_comm_results);
   }
   else
   {
      CuAssertPtrNotNull (tc, check_comm_results);
      CuAssert (tc,
                "VHTI_check_commitment should have returned CheckResults",
                0 == VHTI_validate (CHECK_RESULTS, check_comm_results));
      VHTI_free (check_comm_results);
   }
}

void
check_comm_validation (CuTest *tc)
{
   expect_check_commitment (tc, 0, valid_key_gen_parameters, valid_authority, valid_broadcast_values,
      valid_keyshare_commitment);
   expect_check_commitment (tc, -1, invalid_key_gen_parameters, valid_authority, valid_broadcast_values,
      valid_keyshare_commitment);
   expect_check_commitment (tc, -1, valid_key_gen_parameters, invalid_authority, valid_broadcast_values,
      valid_keyshare_commitment);
   expect_check_commitment (tc, -1, valid_key_gen_parameters, valid_authority, invalid_broadcast_values,
      valid_keyshare_commitment);
   expect_check_commitment (tc, -1, valid_key_gen_parameters, valid_authority, valid_broadcast_values,
      invalid_keyshare_commitment);
}
