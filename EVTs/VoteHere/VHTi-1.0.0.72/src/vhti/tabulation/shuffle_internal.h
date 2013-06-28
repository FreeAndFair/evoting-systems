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
#ifndef __SHUFFLE_INTERNAL_H
#define __SHUFFLE_INTERNAL_H

#include "vhti/types.h"
#include "support/bignum.h"

#ifdef __cplusplus

namespace VHInternal{

int
shuffle_el_gamal_sequence (const char *X_values,
                           const char *Y_values,
                           SignedBlankBallot signed_blank_ballot,
                           GeneralPurposePublicKey ballot_signing_key,
                           RandomState random_state,
                           const char **X_values_out,
                           const char **Y_values_out,
                           RandomState *random_state_out,
                           ShuffleValidityProof *shuffle_validity_proof);

int
generate_secret_shuffle_values(VHUtil::xml_tree &xml_bb,
                               Permutation permutation,
                               const char *beta_ji_values,
                               const char *e_values,
                               int ksize,
                               RandomState random_state,
                               const char **secret_shuffle_values,
                               RandomState *random_state_out);

int
generate_raw_ballot_output(VHUtil::xml_tree &xml_bb,
                           const char * X_values,
                           const char * Y_values,
                           Permutation permutation,
                           RandomState random_state,
                           const char **X_values_out,
                           const char **Y_values_out,
                           const char **beta_ji_values,
                           RandomState *random_state_out);

int
generate_public_shuffle_values(VHUtil::xml_tree &xml_bb,
                               const char * X_values,
                               const char * Y_values,
                               const char *secret_shuffle_values,
                               const char **public_shuffle_values);

int
generate_shuffle_hash_values(VHUtil::xml_tree &xml_bb,
                             const char * X_values,
                             const char * Y_values,
                             const char *public_shuffle_values,
                             const char * X_values_shuf,
                             const char * Y_values_shuf,
                             const char **rho_values);

int
generate_final_shuffle_values(VHUtil::xml_tree &xml_bb,
                              const char *secret_shuffle_values,
                              const char *rho_values,
                              const char **final_shuffle_values,
                              bool & collision);

int
simple_k_shuffle (VHUtil::xml_tree &xml_bb,
                  const char *xvalues,
                  const char *gamma_val,
                  Permutation permutation,
                  const char *nuu_val,
                  RandomState random_state,
                  SimpleShuffleValidityProof *simple_shuffle_validity_proof,
                  RandomState *random_state_out,
                  bool & collision);

} // namespace

#endif  /* __cplusplus */

#endif  /* __SHUFFLE_INTERNAL_H */
