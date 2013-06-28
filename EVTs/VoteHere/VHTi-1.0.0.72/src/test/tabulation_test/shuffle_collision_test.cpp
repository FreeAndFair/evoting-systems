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

#include "tabulation_test.h"
#include <misc/cutest.h>
#include "tabulation/shuffle_internal.h"
#include <stdio.h>
#include "support_test/test-data.h"
#include "vhti/types.h"
#include "misc/xml_tree.h"
#include <malloc.h>

static void
expect_shuffle_collision (CuTest *tc,
                          int expected_status,
                          VHUtil::xml_tree &xml_bb,
                          const char *secret_shuffle_values,
                          const char *rho_values)
{
   const char *final_shuffle_values = 0;
   bool collision = false;

   CuAssert (tc,
             (0 == expected_status
              ? "generate_final_shuffle_values of valid inputs should have succeeded"
              : "generate_final_shuffle_values of invalid inputs should have failed"),
             (expected_status == VHInternal::generate_final_shuffle_values
               (xml_bb,
                secret_shuffle_values,
                rho_values, &final_shuffle_values, collision)));

   if (0 != expected_status)
   {
         fprintf (stderr, "Hmm: generate_final_shuffle_values should have returned 0.");
   }
   else
   {
      if (!collision)
      {
         fprintf(stderr, "Hmm: generate_final_shuffle_values should have had collisions.");
      }
   }
}

void
shuffle_collision_validation (CuTest *tc)
{
   VHUtil::xml_tree xml_bb (valid_bb);

   expect_shuffle_collision (tc, 0, xml_bb, valid_secret_shuffle_values_4b1_collsion,
      valid_rho_hash_values4collision);
   expect_shuffle_collision (tc, 0, xml_bb, valid_secret_shuffle_values_4b2_collsion,
      valid_rho_hash_values4collision);
   expect_shuffle_collision (tc, 0, xml_bb, valid_secret_shuffle_values_4r_collsion,
      valid_rho_hash_values4collision);
}
