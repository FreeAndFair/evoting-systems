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

#ifndef TABULATION_TEST_H
#define TABULATION_TEST_H

#ifdef __cplusplus
extern "C"
{
#endif

#include <misc/cutest.h>

void
auth_validation (CuTest *tc);

void
shuffle_validation (CuTest *tc);

void
shuffle_collision_validation (CuTest *tc);

void
check_shuffle_validation (CuTest *tc);

void
partial_decrypt_validation (CuTest *tc);

void
check_partial_decrypt_validation (CuTest *tc);

void
combine_partial_decrypts_validation (CuTest *tc);

void
gen_pre_vv_results_validation (CuTest *tc);

void
gen_partial_vv_results_validation (CuTest *tc);

void
check_vc_partial_decrypts_and_combine_validation (CuTest *tc);

void
gen_dictionary_secrets_validation (CuTest *tc);

void
check_dictionary_secrets_validation (CuTest *tc);

void
combine_dictionary_secrets_validation (CuTest *tc);

void
initialize_data ();

#ifdef __cplusplus
}
#endif

#endif
