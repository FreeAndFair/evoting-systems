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

#include "vhti/check_shuffle.h"
#include <vhti/random.h>
#include <support/bignum.h>
#include <support/internal_error.h>
#include <support/random_internal.h>
#include <tabulation/tabulation_internal.h>
#include <tabulation/check_internal.h>
#include <support/xml_tree_group_check.h>
#include <support/support_internal.h>
#include <misc/xml_tree.h>
#include <misc/vh_excpt.h>
#include <string.h>
#include <sstream>

int
VHTI_check_shuffle (RawBallotBox raw_ballot_box_before,
                    RawBallotBox raw_ballot_box_after,
                    SignedBlankBallot signed_blank_ballot,
                    GeneralPurposePublicKey ballot_signing_key,
                    ShuffleValidityProof shuffle_validity_proof,
                    CheckResults *check_shuffle_result)
{
   int result = 0; // Assume success until told otherwise
   int icount = 0; // A counter used for loops
   *check_shuffle_result = 0;
   auto_BN pm(NULL); // The Election Modulus
   auto_BN qm(NULL); // The Election Subgroup Modulus
   auto_BN gen(NULL); // The Election Subgroup Generator
   auto_BN ePublicKey(NULL); // The Election Public Key
   
   try {
      result = (::VHTI_validate(RAW_BALLOT_BOX, raw_ballot_box_before)
         || ::VHTI_validate(RAW_BALLOT_BOX, raw_ballot_box_after)
         || ::VHTI_validate(SHUFFLE_VALIDITY_PROOF, shuffle_validity_proof));
      
      if (result != 0) throw VH_exception("VALIDATION_FAILURE");
      // An empty xml tree for CheckResults
      VHUtil::xml_tree xml_res("<" CHECK_RESULTS "/>");

      // An xml tree from the signed_blank_ballot input
      VHUtil::xml_tree_group_check xml_bb(signed_blank_ballot,
                                           BLANK_BALLOT,
                                           ballot_signing_key,
                                           pm, qm, gen, ePublicKey);
      VHUtil::xml_node root_bb = xml_bb.root();
      // Check the shuffle_validity_proof input
      VHUtil::xml_tree_group_check xml_svp(shuffle_validity_proof, pm, qm, gen, ePublicKey);
      
      // An xml tree from raw_ballot_box_before input
      VHUtil::xml_tree_group_check xml_rbb_before(raw_ballot_box_before,
         pm, qm, gen, ePublicKey);
      // The root node of xml_rbb_before
      VHUtil::xml_node root_rbb_before = xml_rbb_before.root();
      // An xml tree from raw_ballot_box_after
      VHUtil::xml_tree_group_check xml_rbb_after(raw_ballot_box_after,
         pm, qm, gen, ePublicKey);
      // The root node of xml_rbb_after
      VHUtil::xml_node root_rbb_after = xml_rbb_after.root();
      
      // An empty xml tree to hold the unshuffled X values
      VHUtil::xml_tree xml_X_before("<XValues/>");
      // The root node of xml_X_before
      VHUtil::xml_node root_X_before = xml_X_before.root();
      // An empty xml tree to hold the unshuffled Y values
      VHUtil::xml_tree xml_Y_before("<YValues/>");
      // The root node of xml_Y_before
      VHUtil::xml_node root_Y_before = xml_Y_before.root();
      // An empty xml tree to hold the shuffled X values
      VHUtil::xml_tree xml_X_after("<XValues/>");
      // The root node of xml_X_after
      VHUtil::xml_node root_X_after = xml_X_after.root();
      // An empty xml tree to hold the shuffled Y values
      VHUtil::xml_tree xml_Y_after("<YValues/>");
      // The root node of xml_Y_after
      VHUtil::xml_node root_Y_after = xml_Y_after.root();
      
      int num_ballots = root_rbb_before->element_count(); // Number of ballots
      // Number of questions per ballot
      int num_questions = 0; // How many questions in a ballot
      int num_elems_bb = root_bb->element_count();
      for (int i_bb=0; i_bb<num_elems_bb; i_bb++)
      {
         if (root_bb->e(i_bb)->name() == BALLOT_QUESTION)
         {
            num_questions++;
         }
      }
      for (int nb=0; nb<num_ballots; nb++)
      {
         // A node for xml_balX_before
         VHUtil::xml_node root_balX_before =
            root_X_before->new_element("Ballot");
         // A node for xml_balY_before
         VHUtil::xml_node root_balY_before =
            root_Y_before->new_element("Ballot");
         // A node for xml_balX_after
         VHUtil::xml_node root_balX_after = root_X_after->new_element("Ballot");
         // A node for xml_balY_after
         VHUtil::xml_node root_balY_after = root_Y_after->new_element("Ballot");
         // The current unshuffled ballot
         VHUtil::xml_node cur_ballot_before = root_rbb_before->e(nb);
         // The current shuffled ballot
         VHUtil::xml_node cur_ballot_after = root_rbb_after->e(nb);
         
         for (int nq=0; nq<num_questions; nq++)
         {  // The current answer of the current unshuffled ballot
            VHUtil::xml_node cur_answer_before = cur_ballot_before->e(nq);
            // The current answer of the current shuffled ballot
            VHUtil::xml_node cur_answer_after = cur_ballot_after->e(nq);
            
            add_BN_element(root_balX_before, X_VALUE,
               xml2BN(cur_answer_before->e(X_VALUE)));
            add_BN_element(root_balY_before, Y_VALUE,
               xml2BN(cur_answer_before->e(Y_VALUE)));
            add_BN_element(root_balX_after, X_VALUE,
               xml2BN(cur_answer_after->e(X_VALUE)));
            add_BN_element(root_balY_after, Y_VALUE,
               xml2BN(cur_answer_after->e(Y_VALUE)));
         }
      }
      std::ostringstream oss_Xb; // A stream to hold xml_X_before
      oss_Xb << xml_X_before;
      std::ostringstream oss_Yb; // A stream to hold xml_Y_before
      oss_Yb << xml_Y_before;
      std::ostringstream oss_Xa; // A stream to hold xml_X_after
      oss_Xa << xml_X_after;
      std::ostringstream oss_Ya; // A stream to hold xml_Y_after
      oss_Ya << xml_Y_after;
      
      // The returned products of all the X values for each ballot
      auto_freeing< ConstCharStar > X_hats = 0;
      // The returned products of all the Y values for each ballot
      auto_freeing< ConstCharStar > Y_hats = 0;
      // The returned products of all the Xbar values for each ballot
      auto_freeing< ConstCharStar > X_checks = 0;
      // The returned products of all the Ybar values for each ballot
      auto_freeing< ConstCharStar > Y_checks = 0;
      // The random exponents for each question
      auto_freeing< ConstCharStar > e_values = 0;
      
      VHInternal::generate_el_gamal_sequences
         (xml_bb,
          oss_Xb.str().c_str(), oss_Yb.str().c_str(), oss_Xa.str().c_str(),
          oss_Ya.str().c_str(), &X_hats, &Y_hats, &X_checks, &Y_checks,
          &e_values);
      
      // The result of check_shuffle_el_gamal_sequence
      auto_freeing<CheckResults> check_shuffle_egs_result = 0;
      VH_propagate(VHInternal::check_shuffle_el_gamal_sequence
                   ( xml_bb,
                     X_hats, Y_hats,
                     X_checks, Y_checks,
                     shuffle_validity_proof,
                     &check_shuffle_egs_result), CHECK_SHUFFLE);
      
      if (check_shuffle_result) {
         *check_shuffle_result = VHTI_dup(check_shuffle_egs_result);
      }
   }
   catch (const VHUtil::Exception & e) {
      VHTI_set_last_error(e);
      result = e.getResultNo();
   }
   
   return result;
}
