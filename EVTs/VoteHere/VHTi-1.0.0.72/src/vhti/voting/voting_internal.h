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
#ifndef __VOTING_INTERNAL_H
#define __VOTING_INTERNAL_H

#include "vhti/types.h"
#include "misc/xml_tree.h"
#include "support/random_internal.h"
#include <openssl/bn.h>

#ifdef __cplusplus

namespace VHInternal{

void
generate_verification_code (VHUtil::xml_node & vv_keys,
                            VHUtil::xml_node & blank_ballot,
                            VHUtil::xml_node & bsn,
                            VHUtil::xml_node & answer_ref,
                            int vv_len,
                            std::string & vv_alphabet,
                            VoteVerificationCode * vv_code);

void
generate_vote_receipt_data (std::string & svb_data,
                            VHUtil::xml_node &  vv_keys,
                            VHUtil::xml_node &  blank_ballot,
                            VHUtil::xml_node &  bsn,
                            VHUtil::xml_node &  clear_text_ballot,
                            int vv_len,
                            std::string & vv_alphabet,
                            VoteReceiptData * vote_receipt_data);

void
generate_vote_verification_dictionary (VHUtil::xml_node & root_vv_keys,
                                       VHUtil::xml_node & root_blank_ballot,
                                       VHUtil::xml_node & root_bsn,
                                       int vv_len,
                                       std::string & str_vv_alphabet,
                                       VoteVerificationDictionary * vv_dictionary);


void
   check_correct_number_of_answers (const unsigned int num_answers,
                                    VHUtil::xml_tree::node *xml_bb);

void
encrypt_answer(const VHUtil::xml_node &answer,
               const BIGNUM *subgroup_generator,
               const BIGNUM *modulus,
               const BIGNUM *subgroup_order,
               const BIGNUM *ePublicKey,
               VHUtil::xml_tree::node *egp_destination,
               VHInternal::RS &rs);

/*
void
generate_answer_validity_proofs (VHUtil::xml_node &  root_blank_ballot,
                                 VHUtil::xml_node & root_raw_voted_ballot,
                                 VHUtil::xml_node & root_random_state,
                                 AnswerValidityProofs * answer_validity_proofs);

void
check_answer_validity_proofs (VHUtil::xml_node &  root_blank_ballot,
                              VHUtil::xml_node & root_answer_validity_proofs,
                              VHUtil::xml_node & root_raw_voted_ballot,
                              CheckResults * check_results);

*/
} // namespace

#endif  /* __cplusplus */

#endif  /* __VOTING_INTERNAL_H */
