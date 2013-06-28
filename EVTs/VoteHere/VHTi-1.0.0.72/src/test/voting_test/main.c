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

#include <libxml/tree.h>
#include <libxml/parser.h>
#include <vhti/support.h>
#include <openssl/rand.h>

#include <misc/cutest.h>
#include "voting_test.h"
#include <stdio.h>

CuSuite *my_suite = 0;

int
main ()
{
   CuString *output = CuStringNew();
   
   // Initialize openssl and libxml
   int rnd_seed = 0;
   xmlInitParser();

   my_suite = CuSuiteNew();

   SUITE_ADD_TEST(my_suite, encrypt_ballot_pollsite_validation);
   SUITE_ADD_TEST(my_suite, gen_vvcode_validation);
   SUITE_ADD_TEST(my_suite, gen_vote_receipt_data_validation);
   SUITE_ADD_TEST(my_suite, sign_receipt_validation);
   SUITE_ADD_TEST(my_suite, gen_vote_receipt_data_validation);
   SUITE_ADD_TEST(my_suite, gen_vote_verification_dictionary_validation);
   
   initialize_data ();
   
   CuSuiteRun (my_suite);
   CuSuiteSummary (my_suite, output);
   CuSuiteDetails (my_suite, output);
   printf("%s\n", output->buffer);
   
   return (my_suite->failCount
      ? 1
      : 0);
}
