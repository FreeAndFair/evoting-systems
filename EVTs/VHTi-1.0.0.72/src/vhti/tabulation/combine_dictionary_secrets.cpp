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

#include "vhti/combine_dictionary_secrets.h"
#include "vhti/sign.h"
#include "vhti/random.h"
#include <support/support_internal.h>
#include <support/internal_error.h>
#include <support/random_internal.h>
#include <support/bignum.h>
#include <support/xml_tree_group_check.h>
#include <misc/vh_excpt.h>
#include <misc/xml_tree.h>
#include <util/sslerror.h>
#include <string>
#include <sstream>

// Anybody can call this function using any of the commitments
// to check the revealed secrets

int
VHTI_combine_dictionary_secrets (TrusteeRevealedDictionarySecrets trustee_dict_secrets_box,
                                 BlankBallot blank_ballot,
                                 int vv_len,
                                 AlphabetEncoding vv_alphabet,
                                 VoteVerificationDictionaries *verification_dictionaries)
{
   int result = 0; // Assume success until told otherwise
   int check_res = 0;
   int bsn_compare_result = 0; // The result of comparing two bsns
   auto_BN pm(NULL); // The Election Modulus
   auto_BN qm(NULL); // The Election Subgroup Modulus
   auto_BN gen(NULL); // The Election Subgroup Generator
   auto_BN ePublicKey(NULL); // The Election Public Key
   // An OpenSSL structure that holds BIGNUM temporary variables used by
   // library functions
   auto_BN_CTX ctx(BN_CTX_new());
   *verification_dictionaries = NULL;
   
   try
   {
      VH_nonzero (ctx, BN_CTX_NEW);
      
      VH_zero(::VHTI_validate(TRUSTEE_REVEALED_DICTIONARY_SECRETS_BOX,
         trustee_dict_secrets_box), VALIDATION_FALIURE);
      VH_zero(::VHTI_validate(BLANK_BALLOT, blank_ballot), VALIDATION_FAILURE);
      VH_zero(::VHTI_validate(ALPHABET_ENCODING, vv_alphabet), VALIDATION_FAILURE);

       // An xml tree from the blank_ballot input
      VHUtil::xml_tree_group_check xml_bb(blank_ballot, pm, qm, gen, ePublicKey);
      VHUtil::xml_node root_bb = xml_bb.root();

      // An xml tree from the revealed secrets of all trustees
      VHUtil::xml_tree_group_check xml_secrets_box(trustee_dict_secrets_box,
         pm, qm, gen, ePublicKey);
      VHUtil::xml_node root_secrets_box = xml_secrets_box.root();

      // An xml tree from the alphabet encoding input
      VHUtil::xml_tree_group_check xml_encoding(vv_alphabet, pm, qm, gen, ePublicKey);
      VHUtil::xml_node root_encoding = xml_encoding.root();
      std::string str_vv_alphabet(vv_alphabet);

      // An empty xml tree for the VoteVerificationDictionaries
      VHUtil::xml_tree xml_vv_dicts("<" VOTE_VERIFICATION_DICTIONARIES "/>");
      // The root node of xml_vv_dictss
      VHUtil::xml_node root_vv_dicts = xml_vv_dicts.root();

      // Find out how many trustees
      int num_trustees = root_secrets_box->element_count();

      // Find out how many bsns
      int num_bsns = 0;
      // First Trustee
      VHUtil::xml_node sample_trustee = root_secrets_box->e(0);
      VHUtil::xml_node sample_bsn_rds = sample_trustee->e(BSN_REVEALED_DICTIONARY_SECRETS);
      for (int i=0; i<sample_trustee->element_count(); i++)
      {
         if (sample_trustee->e(i)->name() == BSN_REVEALED_DICTIONARY_SECRETS)
         {
            num_bsns++;
         }
      }
      // Find out how many secrets per BSN
      int num_secrets_per_bsn = 0;
      for (int ij=0; ij<sample_bsn_rds->element_count(); ij++)
      {
         std::string name = sample_bsn_rds->e(ij)->name();
         if (sample_bsn_rds->e(ij)->name() == REVEALED_DICTIONARY_SECRET)
         {
            num_secrets_per_bsn++;
         }
      }


      // Get the secret values in order from each trustee
      for (int j=0; j<num_bsns; j++)
      {
         VHUtil::xml_node vv_dict_node =
               root_vv_dicts->new_element(VOTE_VERIFICATION_DICTIONARY);

         for (int k=0; k<num_secrets_per_bsn; k++)
         {
            auto_BN running_sum;
            BN_zero(running_sum);
            VHUtil::xml_node current_bsn;

            for (int jk=0; jk<num_trustees; jk++)
            {
               VHUtil::xml_node current_trustee = root_secrets_box->e(jk);
               
               VHUtil::xml_node current_bsn_rds =
                  current_trustee->e(BSN_REVEALED_DICTIONARY_SECRETS, j);

               current_bsn = current_bsn_rds->e(BALLOT_SEQUENCE_NUMBER);
               
               VHUtil::xml_node current_secret =
                  current_bsn_rds->e(REVEALED_DICTIONARY_SECRET, k);
               auto_BN secret_val = xml2BN(current_secret);

               VH_nonzero(BN_add(running_sum, running_sum, secret_val), BN_ADD);
               
            }

            if (k == 0)
            {
               vv_dict_node->add_element(current_bsn->deep_copy());
            }

            // Get the corresponding question out of the blank ballot
            VHUtil::xml_node current_question = root_bb->e(BALLOT_QUESTION, k);
            std::string qref = current_question->attribute(QUESTION_REFERENCE);
            // A new node to hold the DictionaryQuestion
            VHUtil::xml_node root_vvd_question =
               vv_dict_node->new_element(DICTIONARY_QUESTION);
            root_vvd_question->add_attribute(QUESTION_REFERENCE, qref);

            // Now raise each answer mark to the total sum
            VHUtil::xml_node current_answer = NULL;
            for (int kk=0;
            current_answer = current_question->element(BALLOT_ANSWER, kk);
            kk++)
            {
               VHUtil::xml_node current_answer =
                  current_question->element(BALLOT_ANSWER, kk);
               if (!current_answer->has_attribute(ANSWER_REFERENCE))
               {
                  throw VHUtil::Exception
                     (__FILE__, __LINE__,
                     "AnswerReference attribute not found");
               }
               // A string of the current answer AnswerReference
               std::string aref = current_answer->attribute(ANSWER_REFERENCE);
               
               VHUtil::xml_node current_am = current_answer->e(ANSWER_MARK);
               auto_BN exp_value;
               if (!BN_zero(exp_value))
                  throw SSL_ERROR;
               if (!BN_mod_exp(exp_value, xml2BN(current_am), running_sum, pm, ctx))
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
               
               // Add verification code into dictionary
               VHUtil::xml_node root_dict_vc =
                  root_vvd_question->new_element(DICTIONARY_VERIFICATION_CODE);
               root_dict_vc->add_attribute(ANSWER_REFERENCE, aref);

               add_BN_characters(root_dict_vc, bn_vcode, str_vv_alphabet);
            }
         }
      }
      std::ostringstream oss;
      oss << xml_vv_dicts;
      *verification_dictionaries = VHTI_dup(oss.str().c_str());
  }
   catch (const VHUtil::Exception & e)
   {
      VHTI_set_last_error(e);
      result = e.getResultNo();
   }
   return result;
}
