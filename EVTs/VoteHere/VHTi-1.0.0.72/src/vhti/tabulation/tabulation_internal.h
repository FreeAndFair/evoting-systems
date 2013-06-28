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

#ifndef __TABULATION_INTERNAL_H
#define __TABULATION_INTERNAL_H

#include "vhti/types.h"
#include "misc/xml_tree.h"
#include "support/bignum.h"

#ifdef __cplusplus

namespace VHInternal{


void
generate_el_gamal_sequences(VHUtil::xml_tree &xml_bb,
                            const char * X_values,
                            const char * Y_values,
                            const char * X_values_out,
                            const char * Y_values_out,
                            const char **X_hats,
                            const char **Y_hats,
                            const char **X_checks,
                            const char **Y_checks,
                            const char **e_values);

std::vector< int >
get_permutation_vector_from_xml(Permutation permutation);

void
combine_pre_vv_results (PreVerificationCodeBoxes all_trustee_pre_vcodes,
                        VHUtil::xml_tree &blank_ballot,
                        RawBallotBox * verification_raw_ballot_box);

void
check_partial_decrypts_and_combine(SignedBlankBallot signed_blank_ballot,
                                   GeneralPurposePublicKey ballot_signing_key,
                                   PartiallyDecryptedBallotBox pd_ballot_box,
                                   RawClearTextBallots *raw_clear_text_ballots,
                                   CheckResults *combine_partial_decrypt_result);

} // namespace

#endif  /* __cplusplus */

#endif  /* __TABULATION_INTERNAL_H */
