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

#include <vhti/gen_blank_ballot.h>
#include <vhti/gen_answer_mark.h>
#include <vhti/random.h>
#include <support/internal_error.h>
#include <support/random_internal.h>
#include <support/support_internal.h>
#include <support/bignum.h>
#include <support/xml_tree_group_check.h>
#include <misc/xml_tree.h>
#include "pki/misc.h"           // for SSL_ERROR

#include <string>
#include <sstream>
#include <set>

int
VHTI_generate_blank_ballot (BallotSkeleton ballot_skeleton,
                            CryptoElectionParameters cep,
                            AlphabetEncoding encoding,
                            BlankBallot * blank_ballot)
{
   int result = 0; // Assume success until told otherwise
   *blank_ballot = NULL;
   auto_BN pm(NULL); // The Election Modulus
   auto_BN qm(NULL); // The Election Subgroup Modulus
   auto_BN gen(NULL); // The Election Subgroup Generator
   auto_BN ePublicKey(NULL); // The Election Public Key

   try {
      result = (::VHTI_validate (BALLOT_SKELETON, ballot_skeleton)
                || ::VHTI_validate (CRYPTO_ELECTION_PARAMETERS, cep)
                || ::VHTI_validate (ALPHABET_ENCODING, encoding));
      
      if (result != 0) throw VH_exception("VALIDATION_FAILURE");
      // An empty xml tree to hold the BlankBallot
      VHUtil::xml_tree xml_bb("<" BLANK_BALLOT "/>"); // The root node of xml_bb

      // An xml tree from the CryptoElectionParameters input
      VHUtil::xml_tree_group_check xml_cep(cep, pm, qm, gen, ePublicKey);
      // An xml tree from the ballot_skeleton input
      VHUtil::xml_tree_group_check xml_balskel(ballot_skeleton, pm, qm, gen, ePublicKey);

      // Make a random state out of the ballot skeleton and the
      // CryptoElectionParameters to pass to generate_answer_mark.
      auto_freeing<RandomState> random_state = NULL;
      VHUtil::xml_tree xml_key("<" RANDOM_SEED_KEY "/>"); // An xml tree with the key

      xml_key.root ()->add_characters(xml_balskel.str());
      xml_key.root ()->add_characters(xml_cep.str());

      VH_propagate(VHTI_generate_random_state(xml_key.str().c_str(),
                                              &random_state), GEN_RANDOM_STATE_GEN_BB);

      VHInternal::RS rs (static_cast<const char *>(random_state)); // A RandomState object
      
      // Ensure no question has too many answers.
      for (int i=0; i<xml_balskel.root ()->element_count(); i++)
      {  // The node of the current auestion
         VHUtil::xml_node current_question = xml_balskel.root ()->e(i);
         if (current_question->name() == QUESTION_SKELETON)
         {
            // The xml attribute with the number of answers
            unsigned int num_ans_attribute = 0;
            // The number of answer skeletons we have already been through
            unsigned int answer_skeletons_seen = 0;
            
            // At least one of the above two variables must be non-zero.
            
            if (current_question->has_attribute(NUM_ANS))
               num_ans_attribute = VHInternal::int_from_attribute (current_question, NUM_ANS);
            
            for (int j=0; j<current_question->element_count(); j++)
               if (current_question->e(j)->name() == ANSWER_SKELETON)
                  answer_skeletons_seen++;
               
               // they're allowed to include some answer skeletons, OR
               // a NumAns attribute, but not both.  Pity that DTD
               // language is too weak to express this constraint.
               if (answer_skeletons_seen)
                  VH_zero (num_ans_attribute,
                  "NUM_ANS_ATTRIBUTE_AND_ANSWER_SKELETON");
               
               if (num_ans_attribute)
                  VH_zero (answer_skeletons_seen,
                  "NUM_ANS_ATTRIBUTE_AND_ANSWER_SKELETON");
               
               // Now ensure that this question has fewer answers than
               // there are elements in the subgroup.  We originally
               // allowed exactly as many answers, but later decided
               // that `1' is a bad choice for an answer mark.
               
               auto_BN num_answers; // An auto_BN for the number of answers
               VH_nonzero(BN_set_word (num_answers,
                  num_ans_attribute
                  + answer_skeletons_seen),
                  "GEN_BLANK_BALLOT");
               
               VH_nonzero(1 == BN_cmp (qm, num_answers), NUM_ANSWERS_NOT_LESS_THAN_SUBGROUP_ORDER);
         }
      }

      // Put ElectionID, PrecinctID & CryptoElectionParameters into Blank Ballot
      xml_bb.root ()->add_element(xml_balskel.root ()->e(ELECTION_ID)->deep_copy());
      xml_bb.root ()->add_element(xml_balskel.root ()->e(PRECINCT_ID)->deep_copy());
      xml_bb.root ()->add_element(xml_cep.root()->deep_copy());

      // Put BallotQuestions into Blank Ballot
      VHUtil::xml_node current_question = NULL; // Node of the current question
      int num_answer = 0; // What answer we are currently working on
      for (int i2=0;
           current_question = xml_balskel.root ()->element(QUESTION_SKELETON, i2);
           i2++)
      {
         // A set to keep track of which answer marks we have already used
         // Note that this set starts out empty for each question;
         // this allows an answer mark to appear twice on a given
         // ballot.  The thing we're trying to avoid is having the
         // same mark appear twice in a given *question*.
         std::set<auto_BN> used_marks;

         // A node for a BallotQuestion in the BlankBallot
         VHUtil::xml_node root_bq = xml_bb.root ()->new_element(BALLOT_QUESTION);
         // Use the provided QuestionReference or assign one if missing
         if (current_question->has_attribute(QUESTION_REFERENCE)) {
            root_bq->add_attribute(QUESTION_REFERENCE,
                                   current_question->attribute(QUESTION_REFERENCE));
         }
         else
         {
            std::ostringstream ref_str; // Stream to hold the QuestionReference
            ref_str<< "Q" << i2;
            root_bq->add_attribute(QUESTION_REFERENCE, ref_str.str());
         }
         
         // Use provided QuestionTextStructure or provide empty one if missing
         if (current_question->element(QUESTION_TEXT_STRUCTURE) != NULL) {
            root_bq->add_element(current_question->
                                 e(QUESTION_TEXT_STRUCTURE)->deep_copy ());
         }
         else {
            root_bq->new_element(QUESTION_TEXT_STRUCTURE);
         }
         
         if (current_question->has_attribute(NUM_ANS))
         {  // Put in some empty AnswerSkeleton nodes
            const int num_q_answers = VHInternal::int_from_attribute (current_question, NUM_ANS);
            for (int acount=0; acount<num_q_answers; acount++) {
               current_question->new_element(ANSWER_SKELETON);
            }
         }
         
         // The node of the current answer
         VHUtil::xml_node current_answer = NULL;
         for (int j=0;
              current_answer = current_question->element(ANSWER_SKELETON, j);
              j++)
         {
            // A node for a BallotAnswer in the BlankBallot
            VHUtil::xml_node root_ans = root_bq->new_element(BALLOT_ANSWER);
            
            // Use the provided AnswerReference or assign one if missing
            if (current_answer->has_attribute(ANSWER_REFERENCE)) {
               root_ans->add_attribute(ANSWER_REFERENCE,
                                       current_answer->attribute(ANSWER_REFERENCE));
            }
            else {
               std::string a_letter("A"); // For the AnswerReference
               std::ostringstream j_str;  // A stream for the answer number
               j_str << num_answer;
               // A string representing the AnswerReference
               std::string aref = a_letter + j_str.str();
               root_ans->add_attribute(ANSWER_REFERENCE, aref);
               num_answer++;
            }
            
            // Use provided AnswerTextStructure or provide empty one if missing
            if (current_answer->element(ANSWER_TEXT_STRUCTURE) != NULL) {
               root_ans->add_element(current_answer->
                                     e(ANSWER_TEXT_STRUCTURE)->deep_copy ());
            }
            else {
               root_ans->new_element(ANSWER_TEXT_STRUCTURE);
            }
            
            // Keep generating answer marks until we see one that
            // we haven't seen before.  This loop will execute more
            // than once only when the subgroup order is very small
            // -- i.e., during testing.
            
            // TODO -- this may be overkill; it might suffice to
            // merely ensure that answer marks are unique per
            // question, not per ballot.
            {
               auto_BN answer_mark; // The value of the answer mark
               // The answer mark xml we will get back
               auto_freeing<AnswerMark>  answer_mark_xml = 0;
               
               do {
                  VH_propagate(VHTI_generate_answer_mark (xml_cep.root()->e(CRYPTO_GROUP_PARAMETERS)->str().c_str(),
                                                          encoding, rs, &answer_mark_xml, rs), "GEN_BLANK_BALLOT");
                  
                  answer_mark = xml2BN((VHUtil::xml_tree
                                        ((const char *) answer_mark_xml)).root ());
                  
               } while (used_marks.end ()
                        !=
                        used_marks.find (answer_mark));
               
               add_BN_element(root_ans, ANSWER_MARK, answer_mark, DEC);
               used_marks.insert (answer_mark);
            }
         }
      }

      // Put DisplayInfo into BlankBallot
      if (xml_balskel.root ()->element(BALLOT_TEXT_STRUCTURE) != NULL) {
         xml_bb.root ()->add_element(xml_balskel.root ()->e(BALLOT_TEXT_STRUCTURE)->deep_copy());
      }
      else {
         xml_bb.root ()->new_element(BALLOT_TEXT_STRUCTURE);
      }

      *blank_ballot = VHTI_dup(xml_bb.str().c_str());
   }
   catch (const VHUtil::Exception & e) {
      VHTI_set_last_error(e);
      result = e.getResultNo();
   }
   return result;
}
