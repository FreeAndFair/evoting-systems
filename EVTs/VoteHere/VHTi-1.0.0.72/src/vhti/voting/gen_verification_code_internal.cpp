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

#include "voting/voting_internal.h"
#include <support/internal_error.h>
#include <support/random_internal.h>
#include <support/support_internal.h>
#include <support/bignum.h>
#include <support/xml_tree_group_check.h>
#include <support/sanity.h>
#include <misc/xml_tree.h>
#include <util/sslerror.h>
#include <string>
#include <sstream>

void
VHInternal::generate_verification_code (VHUtil::xml_node & root_vv_keys,
                                        VHUtil::xml_node & root_blank_ballot,
                                        VHUtil::xml_node & root_bsn,
                                        VHUtil::xml_node & root_answer_ref,
                                        int vv_len,
                                        std::string &  str_vv_alphabet,
                                        VoteVerificationCode * vv_code)
{
   int icount=0; // A counter used for loops
   auto_BN pm(NULL); // The Election Modulus
   auto_BN qm(NULL); // The Election Subgroup Modulus
   auto_BN gen(NULL); // The Election Subgroup Generator
   auto_BN ePublicKey(NULL); // The Election Public Key
   // An OpenSSL structure that holds BIGNUM temporary variables
   // used by library functions
   auto_BN_CTX ctx(BN_CTX_new());
   if (!ctx) throw SSL_ERROR;
   *vv_code = NULL;
   
   VHInternal::sanity_check_blank_ballot (root_blank_ballot);
   
   // Make container for the verification code
   VHUtil::xml_tree xml_vcode("<" VOTE_VERIFICATION_CODE "/>");
   // The root node of xml_vcode
   VHUtil::xml_node root_vcode = xml_vcode.root();

   VHInternal::get_election_parameters2(root_blank_ballot, pm, qm, gen, ePublicKey);
   
   auto_BN i_index = xml2BN(root_bsn); // An index associated with one voter
   auto_BN ans_mark(NULL); // Find AnswerMark that goes with this AnswerRef
   auto_BN j_index; // An index relating to the current question
   std::string current_qref;  // The current QuestionReference as a string
   // The node of the current question
   VHUtil::xml_node current_question = NULL;

   for (int i=0;
        current_question = root_blank_ballot->element(BALLOT_QUESTION, i);
        i++)
   {
      VHUtil::xml_node current_ans = NULL; // The node of the current answer
      for (int j=0;
           current_ans = current_question->element(BALLOT_ANSWER, j);
           j++)
      {
         if (current_ans->attribute(ANSWER_REFERENCE) ==
             root_answer_ref->characters())
         {
            ans_mark = xml2BN(current_ans->e(ANSWER_MARK));

            // Store the QuestionRef associated with this answer
            current_qref = current_question->attribute(QUESTION_REFERENCE);
            j_index = BN_bin2bn( (unsigned char *)current_qref.c_str(),
                                 current_qref.size(), 0);
            if (!j_index) throw SSL_ERROR;
         }
      }
   }

   if (!ans_mark)
      VHUtil::_check (("NO_MATCHING_ANSWER_REF for `"
                       + root_answer_ref->characters()
                       + "'").c_str (),
                      __FILE__,
                      __LINE__);

   // Need to generate a secret for each authority
   std::vector< auto_BN > alpha_vec; // A vector to hold the alpha values
   auto_BN alpha_sum;
   if (!BN_zero(alpha_sum))
      throw SSL_ERROR;
   for (icount=0; icount<root_vv_keys->element_count(); icount++)
   {  // Seed a RandomIJState with the VoteVerificationKey
      // First build up a RandomIJState object
      VHUtil::xml_tree xml_rij_state("<" RANDOM_IJ_STATE "/>");
      // The root node of xml_rij_state
      VHUtil::xml_node root_rij_state = xml_rij_state.root();
      root_rij_state->add_attribute(SOURCE_TYPE, VHInternal::SourceType);
      
      // An node to hold the RandomSeedKey
      VHUtil::xml_node root_key =
         root_rij_state->new_element(RANDOM_SEED_KEY);
      std::string key_data(root_vv_keys->e(icount)->characters());
      root_key->add_characters(key_data);

      // Get a random alpha_ij in Zq*,
      auto_BN alpha; // where i is the bsn and j is the QuestionReference
      auto_BN one_bn; // An auto_BN with the value of 1
      if (!BN_one(one_bn))
         throw SSL_ERROR;
      // The returning random state
      auto_freeing <RandomState> return_random_state = 0;
      VHInternal::rand_range_2ij (one_bn,
                                  qm,
                                  i_index,
                                  j_index,
                                  xml_rij_state.str().c_str(),
                                  &return_random_state,
                                  alpha);
      // We actually don't use the return_random_state
      // because we always make a new one
      
      if (!BN_add(alpha_sum, alpha_sum, alpha))
         throw SSL_ERROR;
   }
   
   // Now you have the sum of the alphas,
   // now raise the AnswerMark to this sum
   auto_BN exp_value;
   if (!BN_zero(exp_value))
      throw SSL_ERROR;
   if (!BN_mod_exp(exp_value, ans_mark, alpha_sum, pm, ctx))
      throw SSL_ERROR;
   
   // Now hash this value and return vv_len number of bits.
   // An array to hold the item(s) to hash
   const BIGNUM * arr[] = {exp_value};
   auto_BN hashval;
   hashval = GetHashOfNBNs(arr, sizeof(arr) / sizeof(arr[0]));
   // An auto_BN to hold the verification code
   auto_BN bn_vcode;
   if (!BN_rshift(bn_vcode, hashval, (VHInternal::digest_bits - vv_len)))
      throw SSL_ERROR;
   
   add_BN_characters(root_vcode, bn_vcode, str_vv_alphabet);
   root_vcode->add_attribute(QUESTION_REFERENCE, current_qref);
   std::ostringstream vcode_stream; // A stream to hold xml_vcode
   vcode_stream << xml_vcode;
   *vv_code = VHTI_dup(vcode_stream.str().c_str());
}

