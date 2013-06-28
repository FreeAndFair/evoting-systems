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

#include "vhti/check_pds_and_combine.h"
#include "vhti/check_partial_decrypt.h"
#include "misc/xml_tree.h"
#include <tabulation/tabulation_internal.h>
#include <support/internal_error.h>
#include <support/bignum.h>
#include <support/xml_tree_group_check.h>
#include <support/sanity.h>
#include <string.h>
#include <sstream>
#include <vector>
#include <map>

namespace {
   
typedef std::pair<
   auto_BN,                     // answer mark
   unsigned int                 // question index -- 0 for the first
                                // question in the blank ballot, 1
                                // for the next, etc.
   > map_key;

// Make a mapping from answer marks and question indices to answer
// references
std::map<map_key, std::string>  make_map (VHUtil::xml_tree &bb_tree)
{
   std::map<map_key, std::string> return_value;

   // An xml node of the ballot question
   VHUtil::xml_tree::node *question = 0;
   for (int questions_examined = 0;
        question = bb_tree.root ()->element(BALLOT_QUESTION, questions_examined);
        questions_examined++)
   {
      // An xml node of the ballot answer
      VHUtil::xml_tree::node *answer = 0;
      for (int answers_examined = 0;
           answer = question->element (BALLOT_ANSWER, answers_examined);
           answers_examined++)
      {
         auto_BN am = xml2BN (answer->e (ANSWER_MARK));
         const std::string aref = answer->attribute (ANSWER_REFERENCE);
         const map_key key (am, questions_examined);

         // add a value of this answer's reference,
         // with a key of this answer's answer mark
         return_value[key] = aref;
      }
   }

   return return_value;
}

} // namespace
int
VHTI_check_partial_decrypts_and_combine
(SignedBlankBallot signed_blank_ballot,
 GeneralPurposePublicKey ballot_signing_key,
 PartiallyDecryptedBallotBox pd_ballot_box,
 ClearTextBallots *clear_text_ballots,
 CheckResults *combine_partial_decrypt_result)
{
   // Assume success until told otherwise
   int result = 0;

   *clear_text_ballots = NULL;
   *combine_partial_decrypt_result = NULL;

   auto_BN pm(NULL); // The Election Modulus
   auto_BN qm(NULL); // The Election Subgroup Modulus
   auto_BN gen(NULL); // The Election Subgroup Generator
   auto_BN ePublicKey(NULL); // The Election Public Key
   
   try
   {
      result = (::VHTI_validate(SIGNED_BLANK_BALLOT, signed_blank_ballot)
                || ::VHTI_validate(PARTIALLY_DECRYPTED_BALLOT_BOX, pd_ballot_box));

      if (result != 0) throw VH_exception("VALIDATION_FAILURE");

      // An xml tree from the signed_blank_ballot input
      VHUtil::xml_tree_group_check xml_bb(signed_blank_ballot,
                                          BLANK_BALLOT,
                                          ballot_signing_key,
                                          pm, qm, gen, ePublicKey);
      VHInternal::sanity_check_blank_ballot (xml_bb.root());

      // Check the other input
      VHUtil::xml_tree_group_check xml_pdbb(pd_ballot_box, pm, qm, gen, ePublicKey);
      
      // Raw clear text ballots returned from check_partial_decrypts_and_combine
      auto_freeing< RawClearTextBallots > raw_clear_text_ballots = 0;
      // The results from check_partial_decrypts_and_combine
      auto_freeing<CheckResults> combine_partial_decrypt_result_internal = 0;
      VHInternal::check_partial_decrypts_and_combine
         (signed_blank_ballot,
          ballot_signing_key,
          pd_ballot_box,
          &raw_clear_text_ballots,
          &combine_partial_decrypt_result_internal);

      *combine_partial_decrypt_result =
         VHTI_dup(combine_partial_decrypt_result_internal);
      
      if (strstr (*combine_partial_decrypt_result, CHECK_SUCCESS_TEXT))
      {
         // An empty xml tree to hold the ClearTextBallots
         VHUtil::xml_tree xml_ctbs("<" CLEAR_TEXT_BALLOTS "/>");
         // The root node of xml_ctbs
         VHUtil::xml_node root_ctbs = xml_ctbs.root();
      
         // A map relating answer marks and question indices to answer
         // references
         std::map<map_key, std::string> aref_map (make_map (xml_bb));
      
         // A string made from the raw_clear_text_ballots input
         std::string str_raw_ctbs(raw_clear_text_ballots);
         // An xml tree of str_raw_ctbs
         VHUtil::xml_tree xml_raw_ctbs(str_raw_ctbs);
         // The root node of xml_raw_ctbs
         VHUtil::xml_node root_raw_ctbs = xml_raw_ctbs.root();
         // The number of raw clear text ballots
         int num_ballots = root_raw_ctbs->element_count();
         for (int i=0; i<num_ballots; i++)
         {
            // The current ballot
            VHUtil::xml_node current_raw_ctb = root_raw_ctbs->e(i);
            // The number of answers in the current ballot
            int num_ans = current_raw_ctb->element_count();
         
            // An new node in ClearTextBallots to hold a ClearTextBallot
            VHUtil::xml_node root_ctb = root_ctbs->new_element(CLEAR_TEXT_BALLOT);
         
            for (int j=0; j<num_ans; j++)
            {
               // The current answer mark
               auto_BN current_answer_mark = xml2BN(current_raw_ctb->e(j));
            
               // Add this AnswerReference to the ClearTextBallot structure
               // A node for the AnswerReference
               VHUtil::xml_tree::node *ar =
                  root_ctb->new_element (ANSWER_REFERENCE);
               // An iterator which points to the answer mark in the map
               std::map<map_key, std::string>::iterator ref_iter =
                  aref_map.find (map_key (current_answer_mark, j));
            
               if (ref_iter == aref_map.end ())
               {
                  // The voter apparently encrypted some bogus value
            
                  // TODO -- figure out how to deal with this.  If the
                  // vote came from a remote voter, then we should
                  // have detected the problem when we checked the
                  // proof of validity, and thus this should never
                  // happen; that argues for throwing an exception, or
                  // even dying with an assertion failure.  For that
                  // matter, if the vote came from a pollsite voter,
                  // there should also have been a proof (modulo the
                  // fact that, as of December 2003, those proofs
                  // haven't yet been implemented) ... so perhaps
                  // dying *is* the best thing.

                  // A stream to hold an error message
                  std::ostringstream am_error;
                  am_error << "!No answer reference corresponds to answer mark "
                           << current_answer_mark
                           << "!";
                  VHUtil::cout () << am_error.str () 
                                  << std::endl;
                  ar->add_characters (am_error.str ());
               }
               else
               {
                  ar->add_characters (ref_iter->second);
                  // The answer reference associated with the current answer mark
                  std::string answer_ref = ref_iter->second;
               }
            }
         }

         *clear_text_ballots = VHTI_dup(xml_ctbs.str().c_str());
      }
   }
   catch (const VHUtil::Exception & e)
   {
      VHTI_set_last_error(e);
      result = e.getResultNo();
   }
   return result;
}
