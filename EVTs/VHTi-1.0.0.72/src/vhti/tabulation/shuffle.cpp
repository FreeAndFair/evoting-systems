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

#include "vhti/shuffle.h"
#include "vhti/permutation.h"
#include "vhti/random.h"
#include <support/support_internal.h>
#include <tabulation/shuffle_internal.h>
#include "tabulation/private_elements.h"
#include <support/internal_error.h>
#include <support/random_internal.h>
#include <support/bignum.h>
#include <support/xml_tree_group_check.h>
#include <misc/vh_excpt.h>
#include <misc/xml_tree.h>
#include <string>
#include <sstream>

int
VHTI_shuffle (RawBallotBox raw_ballot_box_before,
              RandomState random_state,
              SignedBlankBallot signed_blank_ballot,
              GeneralPurposePublicKey ballot_signing_key,
              RawBallotBox *raw_ballot_box_after,
              RandomState *random_state_out,
              ShuffleValidityProof *shuffle_validity_proof)
{
   int result = 0; // Assume success until told otherwise
   int icount = 0; // A counter used for loops
   *raw_ballot_box_after = NULL;
   *random_state_out = NULL;
   *shuffle_validity_proof = NULL;
   auto_BN pm(NULL); // The Election Modulus
   auto_BN qm(NULL); // The Election Subgroup Modulus
   auto_BN gen(NULL); // The Election Subgroup Generator
   auto_BN ePublicKey(NULL); // The Election Public Key
   
   try {
      result = (::VHTI_validate(RAW_BALLOT_BOX, raw_ballot_box_before)
         || ::VHTI_validate(RANDOM_STATE, random_state)
         || ::VHTI_validate(SIGNED_BLANK_BALLOT, signed_blank_ballot));

      if (result != 0) throw VH_exception("VALIDATION_FAILURE");

      // An xml tree from the signed_blank_ballot input
      VHUtil::xml_tree_group_check xml_sbb(signed_blank_ballot,
                                           BLANK_BALLOT,
                                           ballot_signing_key,
                                           pm, qm, gen, ePublicKey);
      VHUtil::xml_node root_sbb = xml_sbb.root();
      // Make a RawBallotBox(After) out of the RawBallotBox(Before)
      VHUtil::xml_tree_group_check xml_rbb_after_placeholder(raw_ballot_box_before,
         pm, qm, gen, ePublicKey);
      // The root node of xml_rbb_after_placeholder
      VHUtil::xml_node root_rbb_after_placeholder =
         xml_rbb_after_placeholder.root();
      
      // An xml tree from the raw_ballot_box_before input
      VHUtil::xml_tree_group_check xml_rbb(raw_ballot_box_before,
         pm, qm, gen, ePublicKey);
      VHUtil::xml_node root_rbb = xml_rbb.root(); // The root node of xml_rbb
      // Number of ballots in RawBallotBox
      int num_ballots = root_rbb->element_count();
      
      int num_answers = 0; // How many questions in a ballot
      int num_elems_sbb = root_sbb->element_count();
      for (int i=0; i<num_elems_sbb; i++)
      {
         if (root_sbb->e(i)->name() == BALLOT_QUESTION)
         {
            num_answers++;
         }
      }
      
      // Divide ballot box up by ballots
      // An empty xml tree to hold the X values from the whole ballot box
      VHUtil::xml_tree xml_Xvalues("<X_values/>");
      // The root node of xml_Xvalues
      VHUtil::xml_node root_Xvalues = xml_Xvalues.root();
      // An empty xml tree to hold the Y values from the whole ballot box
      VHUtil::xml_tree xml_Yvalues("<Y_values/>");
      // The root node of xml_Yvalues
      VHUtil::xml_node root_Yvalues = xml_Yvalues.root();

      for (icount=0; icount<num_ballots; icount++)
      {  // A node to hold the X values for this ballot
         VHUtil::xml_node root_balX = root_Xvalues->new_element("Ballot");
         // A node to hold the Y values for this ballot
         VHUtil::xml_node root_balY = root_Yvalues->new_element("Ballot");

         for (int j=0; j<num_answers; j++) {
            // The node of the current ballot
            VHUtil::xml_node cur_ballot = root_rbb->e(icount);
            // The node of the current ElGamalPair
            VHUtil::xml_node cur_answer = cur_ballot->e(j);
            root_balX->add_element(cur_answer->e(X_VALUE)->deep_copy());
            root_balY->add_element(cur_answer->e(Y_VALUE)->deep_copy());
         }
      }
      std::ostringstream oss_Xvalues; // A stream to hold xml_Xvalues
      oss_Xvalues << xml_Xvalues;
      std::ostringstream oss_Yvalues; // A stream to hold xml_Yvalues
      oss_Yvalues << xml_Yvalues;
      auto_freeing< ConstCharStar > X_values_out = 0; // The shuffled X values
      auto_freeing< ConstCharStar > Y_values_out = 0; // The shuffled Y values
      // The proof for this shuffle
      auto_freeing< ShuffleValidityProof > shuffle_validity_proof_out = 0;
      // The returning random state
      auto_freeing< RandomState > return_random_state = 0;

      result = VHInternal::shuffle_el_gamal_sequence(oss_Xvalues.str().c_str(),
                  oss_Yvalues.str().c_str(), signed_blank_ballot, ballot_signing_key,
                  random_state, &X_values_out, &Y_values_out, &return_random_state,
                  &shuffle_validity_proof_out);
      if (!result) {
         std::string str_X_out(X_values_out); // String from X_values_out output
         VHUtil::xml_tree xml_Xvalues_out(str_X_out); // xml tree from str_X_out
         // The root node of xml_Xvalues_out
         VHUtil::xml_node root_Xvalues_out = xml_Xvalues_out.root();
         std::string str_Y_out(Y_values_out); // String from Y_values_out output
         VHUtil::xml_tree xml_Yvalues_out(str_Y_out); // xml tree from str_Y_out
         // The root node of xml_Yvalues_out
         VHUtil::xml_node root_Yvalues_out = xml_Yvalues_out.root();
         
         for (int k=0; k<num_ballots; k++)
         {  // Current ballot in the placeholder for the raw ballot box after
            VHUtil::xml_node cur_ballot_out = root_rbb_after_placeholder->e(k);
            // The X values of the current shuffled ballot
            VHUtil::xml_node cur_ballot_shufX = root_Xvalues_out->e(BALLOT,k);
            // The Y values of the current shuffled ballot
            VHUtil::xml_node cur_ballot_shufY = root_Yvalues_out->e(BALLOT,k);

            for (icount=0; icount<num_answers; icount++)
            {  // Current answer in the placeholder for the raw ballot box after
               VHUtil::xml_node cur_answer_out = cur_ballot_out->e(icount);
               cur_answer_out->e (X_VALUE)->erase ();
               cur_answer_out->e (Y_VALUE)->erase ();
               // The value of the current X of the shuffled ballot
               auto_BN bn_XValue = xml2BN (cur_ballot_shufX->e(icount));
               auto_BN bn_YValue = xml2BN (cur_ballot_shufY->e(icount));
               add_BN_element (cur_answer_out, X_VALUE, bn_XValue);
               add_BN_element (cur_answer_out, Y_VALUE, bn_YValue);
            }
         }

         std::ostringstream oss_rbba;
         oss_rbba << xml_rbb_after_placeholder;
         *raw_ballot_box_after = VHTI_dup(oss_rbba.str().c_str());
         *random_state_out = VHTI_dup(return_random_state);
         *shuffle_validity_proof = VHTI_dup(shuffle_validity_proof_out);
      }
   }
   catch (const VHUtil::Exception & e) {
      VHTI_set_last_error(e);
      result = e.getResultNo();
   }
   return result;
}
