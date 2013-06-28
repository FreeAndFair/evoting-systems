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

#ifndef __CHECK_INTERNAL_H
#define __CHECK_INTERNAL_H

#include "vhti/types.h"
#include "support/bignum.h"
#include "misc/xml_tree.h"

#ifdef __cplusplus

namespace VHInternal{

int
generate_simple_check_inputs(VHUtil::xml_tree &xml_bb,
                             ShuffleValidityProof shuffle_validity_proof,
                             const char *rho_values,
                             const char **RValues,
                             const char **SValues);

int
check_values(VHUtil::xml_tree &xml_bb,
             const char *Xvalues_before,
             const char *Yvalues_before,
             const char *Xvalues_after,
             const char *Yvalues_after,
             const char *rho_values,
             ShuffleValidityProof shuffle_validity_proof,
             CheckResults *check_shuffle_answer_result);

int
check_shuffle_el_gamal_sequence(VHUtil::xml_tree &xml_bb,
                                const char *Xhats,
                                const char *Yhats,
                                const char *Xchecks,
                                const char *Ychecks,
                                ShuffleValidityProof shuffle_validity_proof,
                                CheckResults *check_shuffle_answer_result);

int
check_simple_k_shuffle_long(VHUtil::xml_tree &xml_bb,
                            const char *Xvalues,
                            const char *Yvalues,
                            SimpleShuffleValidityProof simple_shuffle_validity_proof,
                            CheckResults *check_simple_shuffle_result);

} // namespace

#endif  /* __cplusplus */

#endif  /* __CHECK_INTERNAL_H */
