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

#include "vhti/enc_ballot_pollsite.h"
#include "vhti/sign.h"
#include "./voting_internal.h"
#include <support/internal_error.h>
#include <support/random_internal.h>
#include <support/support_internal.h>
#include <support/bignum.h>
#include <support/sanity.h>
#include <support/xml_tree_group_check.h>
#include <misc/xml_tree.h>
#include <misc/safe_xml_tree.h>
#include <util/sslerror.h>
#include <string>
#include <sstream>

namespace VHInternal {
void
   check_correct_number_of_answers (const unsigned int num_answers,
                                    VHUtil::xml_tree::node *xml_bb)
{
   for (unsigned int num_questions = 0;
        xml_bb->element(BALLOT_QUESTION,
                        num_questions);
        num_questions++);

   VH_nonzero (num_questions == num_answers, WRONG_NUMBER_OF_ANSWERS);
}
}

int
VHTI_encrypt_ballot_pollsite (ClearTextBallot clear_text_ballot,
                              BlankBallot blank_ballot,
                              BallotSequenceNumber bsn,
                              RandomState random_state,
                              GeneralPurposePrivateKey ballot_signing_key,
                              SignedVotedBallot * signed_voted_ballot,
                              RandomState *random_state_out)
{
   int result = 0; // Assume success until told otherwise
   *signed_voted_ballot = NULL;
   *random_state_out = NULL;
   auto_BN gen(NULL); // ElectionSubgroupGenerator
   auto_BN pm(NULL); // ElectionModulus
   auto_BN qm(NULL); // ElectionSubgroupModulus
   auto_BN ePublicKey(NULL); // ElectionPublicKey

   try {
      VH_zero (::VHTI_validate(CLEAR_TEXT_BALLOT, clear_text_ballot), VALIDATION_FAILURE);
      VH_zero (::VHTI_validate(BLANK_BALLOT, blank_ballot), VALIDATION_FAILURE);
      VH_zero (::VHTI_validate(BALLOT_SEQUENCE_NUMBER, bsn), VALIDATION_FAILURE);
      VH_zero (::VHTI_validate(RANDOM_STATE, random_state), VALIDATION_FAILURE);
      VH_zero (::VHTI_validate(GENERAL_PURPOSE_PRIVATE_KEY,
                               ballot_signing_key), VALIDATION_FAILURE);

      VHInternal::RS rs (random_state); // A RandomState object
      VHUtil::xml_tree_group_check xml_bb(blank_ballot,
                                          pm,
                                          qm,
                                          gen,
                                          ePublicKey);

      VHInternal::sanity_check_blank_ballot (xml_bb.root ());

      // An auto_BN from the BlankBallot
      auto_BN bb_bn = BN_bin2bn(reinterpret_cast<const unsigned char *>(blank_ballot),
                                strlen (blank_ballot), 0);
      if (!bb_bn)
         throw SSL_ERROR;

      const BIGNUM * arr[] = {bb_bn}; // An array of 1 element: the BlankBallot
      auto_BN bbhash = GetHashOfNBNs(arr, sizeof(arr) / sizeof(arr[0]));

      // Create a VotedBallot
      VHUtil::xml_tree xml_vb("<" VOTED_BALLOT "/>");

      {  // The decimal representation of bbhash
         char *decimal_hash = BN_bn2dec(bbhash);
         VH_nonzero (decimal_hash, SSL_ERROR);
         xml_vb.root ()->add_attribute(BB_HASH, decimal_hash);
         OPENSSL_free (decimal_hash);
      }

      // Add in ElectionID and BallotSequenceNumber
      xml_vb.root ()->add_element(xml_bb.root ()->e(ELECTION_ID)->deep_copy());
      xml_vb.root ()->add_element(VHUtil::xml_tree_group_check (bsn, pm, qm, gen, ePublicKey)
                                  .root ()->deep_copy());

      // Create a RawVotedBallot
      VHUtil::xml_node root_rvb = xml_vb.root ()
         ->new_element(RAW_VOTED_BALLOT);

      // Get an answer mark that relates each ClearTextBallot AnswerReference
      // to a BallotAnswer
      // (from BallotQuestion, from BlankBallot, from SignedBlankBallot)
      // An xml tree from the clear_text_ballot input
      VHUtil::xml_tree_group_check xml_ctext(clear_text_ballot,
                                             pm,
                                             qm,
                                             gen,
                                             ePublicKey);

      const unsigned int num_ct_elems = xml_ctext.root()->element_count(); // Number of questions

      VHInternal::check_correct_number_of_answers (num_ct_elems,
                                                   xml_bb.root ());
      
      bool fFoundAnswer = false;

      for (int i=0; i< num_ct_elems; i++)
      {  // Clear text ballots only contain AnswerReference nodes so
         // we don't have to check the node name
         const std::string current_ref(xml_ctext.root()->e(i)->characters());
         VH_nonzero (current_ref.size (), EMPTY_ANSWER_REF);

         // Find the reference in the Blank Ballot and get the corresponding
         // AnswerMark
         VHUtil::xml_node current_question = NULL;
         for (int j=0;
              current_question = xml_bb.root ()->element(BALLOT_QUESTION, j); j++)
         {
            VHUtil::xml_node current_ans = NULL; // The current answer
            for (int k=0;
                 current_ans = current_question->element(BALLOT_ANSWER, k);
                 k++)
            {
               if (current_ans->attribute(ANSWER_REFERENCE) ==
                   current_ref.c_str())
               {
                  VHInternal::encrypt_answer(current_ans,
                                             gen,
                                             pm,
                                             qm,
                                             ePublicKey,
                                             root_rvb,
                                             rs);
                  fFoundAnswer = true;
                  break;
               }
            }
         }

         VH_nonzero (fFoundAnswer, NO_MATCHING_ANSWER_REF);
      }
      
      // Now sign the voted ballot with the secret key

      VH_propagate (VHTI_sign_xml (ballot_signing_key,
                                   xml_vb.str ().c_str (),
                                   signed_voted_ballot),
                    "SIGNING_XML");
      *random_state_out = VHTI_dup (rs);
   }
   catch (const VHUtil::Exception & e)
   {
      VHTI_set_last_error(e);
      result = e.getResultNo();
   }
   return result;
}
