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
#include <vhti/gen_comm.h>
#include <stdio.h>
#include <malloc.h>
#include <support_test/test-data.h>

static void
expect_generate_commitment (CuTest *tc,
                             const int expected_status,
                             KeyGenParameters const key_gen_parameters,
                             Authority const authority,
                             BroadcastValues const broadcast_values,
                             PairwiseSecrets const pairwise_secrets)
{
   char *secret_share = 0;
   char *keyshare_commitment = 0;

   CuAssert (tc,
             (0 == expected_status ?
              "VHTI_generate_commitment should have accepted valid input"
              : "VHTI_generate_commitment should have rejected invalid input"),
             expected_status == VHTI_generate_commitment (key_gen_parameters, authority,
             broadcast_values, pairwise_secrets, &secret_share, &keyshare_commitment));

   if (0 != expected_status)
   {
      if (secret_share)
         fprintf (stderr, "Hmm: `%s'\n", secret_share);
      CuAssertPtrEquals (tc, NULL, secret_share);

      if (keyshare_commitment)
         fprintf (stderr, "Hmm: `%s'\n", keyshare_commitment);
      CuAssertPtrEquals (tc, NULL, keyshare_commitment);
   }
   else
   {
      CuAssertPtrNotNull (tc, secret_share);
      CuAssertPtrNotNull (tc, keyshare_commitment);
      CuAssert (tc,
                "VHTI_generate_commitment should have returned a SecretShare and a KeyShareCommitment",
                0 == ( VHTI_validate (SECRET_SHARE, secret_share)
                && VHTI_validate (KEY_SHARE_COMMITMENT, keyshare_commitment) ) );
      VHTI_free (secret_share);
      VHTI_free (keyshare_commitment);
   }
}

void
gen_comm_validation (CuTest *tc)
{
   expect_generate_commitment (tc, 0, valid_key_gen_parameters, valid_authority, valid_broadcast_values,
      valid_pairwise_secrets);
   expect_generate_commitment (tc, -1, invalid_key_gen_parameters, valid_authority, valid_broadcast_values,
      valid_pairwise_secrets);
   expect_generate_commitment (tc, -1, valid_key_gen_parameters, invalid_authority, valid_broadcast_values,
      valid_pairwise_secrets);
   expect_generate_commitment (tc, -1, valid_key_gen_parameters, valid_authority, invalid_broadcast_values,
      valid_pairwise_secrets);
   expect_generate_commitment (tc, -1, valid_key_gen_parameters, valid_authority, valid_broadcast_values,
      invalid_pairwise_secrets);
}
