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
#include <util/sslerror.h>
#include <string>
#include <sstream>

void
VHInternal::generate_vote_receipt_data (std::string & svb_data,
                                        VHUtil::xml_node & root_vv_keys,
                                        VHUtil::xml_node &  root_blank_ballot,
                                        VHUtil::xml_node &  root_bsn,
                                        VHUtil::xml_node &  root_clear_text_ballot,
                                        int vv_len,
                                        std::string & str_vv_alphabet,
                                        VoteReceiptData * vote_receipt_data)
{
   *vote_receipt_data = NULL;
   
   // Create a VoteReceiptData object
   VHUtil::xml_tree xml_vrd("<" VOTE_RECEIPT_DATA "/>");
   // The root node of xml_vrd
   VHUtil::xml_node root_vrd = xml_vrd.root();

   // Add the bsn
   root_vrd->add_element(root_bsn->deep_copy());
   
   // Get a hash of SignedVotedBallot and add to VoteReceiptData as attribute
   auto_BN svb_bn = BN_bin2bn((unsigned char *)svb_data.c_str(),
      svb_data.size(), 0);
   if (!svb_bn)
      throw SSL_ERROR;
   
   const BIGNUM * arr[] = {svb_bn};
   auto_BN svbhash = GetHashOfNBNs(arr, sizeof(arr) / sizeof(arr[0]));
   {
      char *svb_decimal_hash = BN_bn2dec(svbhash);
      if (0 == static_cast<const char *>(svb_decimal_hash))
         throw SSL_ERROR;
      root_vrd->add_attribute(SVB_HASH, svb_decimal_hash);
      OPENSSL_free (svb_decimal_hash);
   }
   // For each AnswerReference in the ClearTextBallot,
   // get a verification code
   // An node to hold the VoteVerificationCodes
   VHUtil::xml_node root_vcs =
      root_vrd->new_element(VOTE_VERIFICATION_CODES);
   
   {
      for (unsigned int num_questions = 0;
           root_blank_ballot->element (BALLOT_QUESTION, num_questions);
           num_questions++);
      VH_nonzero (num_questions
                  == root_clear_text_ballot->element_count(),
                  WRONG_NUMBER_OF_ANSWERS);
   }
   
   for (int i=0; i<root_clear_text_ballot->element_count(); i++)
   {
      // The current AnswerReference
      VHUtil::xml_node current_answer_ref = root_clear_text_ballot->e(i);
      
      // The returning VoteVerificationCode
      auto_freeing< VoteVerificationCode > verification_code = 0;
      VHInternal::generate_verification_code(root_vv_keys,
         root_blank_ballot, root_bsn, current_answer_ref, vv_len,
         str_vv_alphabet, &verification_code);
      
      // A string holding verification_code
      std::string str_vc(verification_code);
      // An xml tree of str_vc
      VHUtil::xml_tree xml_vc(str_vc);
      // The root node of xml_vc
      VHUtil::xml_node root_vc = xml_vc.root();
      root_vcs->add_element(root_vc->deep_copy());
   }
   
   // A stream to hold xml_vrd
   std::ostringstream vrd_stream;
   vrd_stream << xml_vrd;
   *vote_receipt_data = VHTI_dup(vrd_stream.str().c_str());
}
