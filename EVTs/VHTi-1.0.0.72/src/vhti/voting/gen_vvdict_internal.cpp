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
#include <support/bignum.h>
#include <support/xml_tree_group_check.h>
#include <misc/xml_tree.h>
#include <string>
#include <sstream>

void
VHInternal::generate_vote_verification_dictionary(VHUtil::xml_node & root_vv_keys,
                                                  VHUtil::xml_node & root_blank_ballot,
                                                  VHUtil::xml_node & root_bsn,
                                                  int vv_len,
                                                  std::string & str_vv_alphabet,
                                                  VoteVerificationDictionary * vv_dictionary)
{
   *vv_dictionary = NULL;
   
   // Create a VoteVerificationDictionary object
   VHUtil::xml_tree xml_vvd("<" VOTE_VERIFICATION_DICTIONARY "/>");
   // The root node of xml_vvd
   VHUtil::xml_node root_vvd = xml_vvd.root();
   // Add bsn
   root_vvd->add_element(root_bsn->deep_copy());
   
   // Go through each question on the blank ballot and create a
   // verification code for each answer
   // The node of the current question
   VHUtil::xml_node current_question = NULL;
   for (int i=0;
   current_question = root_blank_ballot->element(BALLOT_QUESTION, i); i++)
   {
      if (!current_question->has_attribute(QUESTION_REFERENCE))
      {
         throw VHUtil::Exception
            (__FILE__, __LINE__,
            "QuestionReference attribute not found");
      }
      
      // A string of the current question QuestionReference
      std::string qref = current_question->
         attribute(QUESTION_REFERENCE);
      // A new node to hold the DictionaryQuestion
      VHUtil::xml_node root_vvd_question =
         root_vvd->new_element(DICTIONARY_QUESTION);
      root_vvd_question->add_attribute(QUESTION_REFERENCE, qref);
      // The current answer node
      VHUtil::xml_node current_answer = NULL;
      for (int j=0;
      current_answer = current_question->element(BALLOT_ANSWER, j);
      j++)
      {
         if (!current_answer->has_attribute(ANSWER_REFERENCE))
         {
            throw VHUtil::Exception
               (__FILE__, __LINE__,
               "AnswerReference attribute not found");
         }
         // A string of the current answer AnswerReference
         std::string aref = current_answer->
            attribute(ANSWER_REFERENCE);
         
         // Make a little AnswerReference xml structure to pass
         // to gen_vcodes
         VHUtil::xml_tree xml_aref("<" ANSWER_REFERENCE "/>");
         // The root node of xml_aref
         VHUtil::xml_node root_aref = xml_aref.root();
         root_aref->add_characters(aref);
         
         // The verification code we create
         auto_freeing< VoteVerificationCode > verification_code = 0;
         VHInternal::generate_verification_code(root_vv_keys,
            root_blank_ballot, root_bsn, root_aref,
            vv_len, str_vv_alphabet, &verification_code);
         
         // A string to hold the verification code
         std::string str_vc(verification_code);
         // An xml tree from str_vc
         VHUtil::xml_tree xml_vc(str_vc);
         // The root node of xml_vc
         VHUtil::xml_node root_vc = xml_vc.root();
         // The value of the verification code
         auto_BN vc_bn = xml2BN(root_vc);
         // Add verification code into dictionary
         VHUtil::xml_node root_dict_vc =
            root_vvd_question->new_element(DICTIONARY_VERIFICATION_CODE);
         root_dict_vc->add_attribute(ANSWER_REFERENCE, aref);
         add_BN_characters(root_dict_vc, vc_bn, str_vv_alphabet);
      }
   }
   // A stream to hold xml_vvd
   std::ostringstream oss_vvd;
   oss_vvd << xml_vvd;
   *vv_dictionary = VHTI_dup(oss_vvd.str().c_str());
}
