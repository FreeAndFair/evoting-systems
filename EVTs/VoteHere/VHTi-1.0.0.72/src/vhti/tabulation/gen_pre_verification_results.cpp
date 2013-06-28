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

#include "vhti/partial_decrypt.h"
#include "vhti/gen_pre_verification_results.h"
#include "misc/xml_tree.h"
#include "misc/safe_xml_tree.h"
#include "util/sslerror.h"
#include <support/internal_error.h>
#include <tabulation/tabulation_internal.h>
#include <support/support_internal.h>
#include <support/random_internal.h>
#include <support/bignum.h>
#include <support/xml_tree_group_check.h>
#include <string.h>
#include <sstream>

int
VHTI_generate_pre_verification_results (VoteVerificationKey vv_key,
                                        SignedVotedBallots signed_voted_ballots,
                                        SignedBlankBallot signed_blank_ballot,
                                        GeneralPurposePublicKey ballot_signing_key,
                                        PreVerificationCodeBox * pre_vcode_box)
{
   int result = 0; // Assume success until told otherwise
   int icount=0; // A counter used for loops
   *pre_vcode_box = NULL;
   auto_BN pm(NULL); // The Election Modulus
   auto_BN qm(NULL); // The Election Subgroup Modulus
   auto_BN gen(NULL); // The Election Subgroup Generator
   auto_BN ePublicKey(NULL); // The Election Public Key
   // An OpenSSL structure that holds BIGNUM temporary variables
   // used by library functions
   auto_BN_CTX ctx(BN_CTX_new());
   if (!ctx) throw SSL_ERROR;
     
   try {
      result = (::VHTI_validate(VOTE_VERIFICATION_KEY, vv_key)
         || ::VHTI_validate(SIGNED_VOTED_BALLOTS, signed_voted_ballots)
         || ::VHTI_validate(SIGNED_BLANK_BALLOT, signed_blank_ballot));
      if (result != 0) throw VH_exception("VALIDATION_FAILURE");
      
      // An xml tree from the signed_blank_ballot input
      VHUtil::xml_tree_group_check xml_bb (signed_blank_ballot,
                                           BLANK_BALLOT,
                                           ballot_signing_key,
                                           pm, qm, gen, ePublicKey);

      // An xml tree from the signed_voted_ballots input
      VHUtil::xml_tree_group_check xml_svbs(signed_voted_ballots, pm, qm, gen, ePublicKey);
       // An xml tree from the vv_key input
      VHUtil::xml_tree_group_check xml_vvk(vv_key, pm, qm, gen, ePublicKey);

      // Seed a RandomIJState with the VoteVerificationKey
      // An empty xml tree to hold the RandomIJState
      VHUtil::xml_tree xml_rij_state("<" RANDOM_IJ_STATE "/>");
      xml_rij_state.root ()->add_attribute(SOURCE_TYPE, VHInternal::SourceType);
      xml_rij_state.root ()->new_element(RANDOM_SEED_KEY)->add_characters(xml_vvk.root ()->characters());

      // A vector of strings that are the question references
      std::vector< std::string > question_vec;
      for (icount=0; icount<xml_bb.root ()->element_count(); icount++)
      {  // The current element in the BlankBallot
         VHUtil::xml_node current_bb_node = xml_bb.root ()->e(icount);
         if (current_bb_node->name() == BALLOT_QUESTION)
         {  // The QuestionReference attribute
            std::string question_ref(current_bb_node->
               attribute(QUESTION_REFERENCE));
            question_vec.push_back(question_ref);
         }
      }
      
      // Make PreVerificationCodes container
      VHUtil::xml_tree xml_pvcb("<" PRE_VERIFICATION_CODE_BOX "/>");
      VHUtil::xml_node root_pvcb = xml_pvcb.root(); // The root node of xml_pvcb
      // Add a node to hold the RawBallotBox
      VHUtil::xml_node root_rbb = root_pvcb->new_element(RAW_BALLOT_BOX);
      
      // The random state returned from rand_range_2ij
      auto_freeing <RandomState> return_random_state = 0;

      for (int i=0; i<xml_svbs.root ()->element_count(); i++)
      {  // Go through all the ballots and generate Xbars and Ybars
         // The current VotedBallot
         std::ostringstream tmp;
         tmp << *(xml_svbs.root ()->element(i));
         VHUtil::safe_xml_tree current_vb (tmp.str (),
                                           VOTED_BALLOT,
                                           "NO_SIGNATURE_CHECK");

         // The current BallotSequenceNumber for this VotedBallot
         VHUtil::xml_node current_bsn =current_vb.root ()->e(BALLOT_SEQUENCE_NUMBER);
         // The current RawVotedBallot of this VotedBallot
         VHUtil::xml_node current_rvb = current_vb.root ()->e(RAW_VOTED_BALLOT);
         auto_BN i_index = xml2BN(current_bsn); // The value of the current_bsn
         
         // For each ElGamal pair, compute encrypted X and Y values
         // and substitute them in the ballot
         for (int j=0; j<current_rvb->element_count(); j++)
         {  // The current ElGamalPair for this RawVotedBallot
            VHUtil::xml_node current_egp = current_rvb->element(j);
            // Use the QuestionRef in the BlankBallot that corresponds
            // to this ElGamal Pair
            // A string of current question reference we are using
            std::string current_qref = question_vec[j];
            // Turn this string into an auto_BN
            auto_BN j_index =BN_bin2bn((unsigned char *)current_qref.c_str(),
                                       current_qref.size(), 0);
            if (!j_index) throw SSL_ERROR;

            auto_BN alpha; // The random number we are going to generate
            auto_BN one_bn; // An auto_BN with the value of 1
            if (!BN_one(one_bn)) throw SSL_ERROR;
            // Get a random alpha_ijk in Zq*, where i is the bsn,
            // j is the QuestionRef, and k is the trustee
            VHInternal::rand_range_2ij(one_bn, qm, i_index,
                                       j_index,
                                       xml_rij_state.str().c_str(),
                                       &return_random_state,
                                       alpha);
            // Don't use the return_random_state because we want the same one
            
            // The node of the X value of the current ElGamal pair
            VHUtil::xml_node X_node = current_rvb->element(j)->e(X_VALUE);
            // The node of the Y value of the current ElGamal pair
            VHUtil::xml_node Y_node = current_rvb->element(j)->e(Y_VALUE);

            // An auto_BN to hold the old X value
            auto_BN old_X_value(xml2BN(X_node));

            // An auto_BN to hold the old Y value
            auto_BN old_Y_value(xml2BN(Y_node));

            auto_BN Xbar; // An auto_BN to hold the new X value
            auto_BN Ybar; // An auto_BN to hold the new Y value

            if (!BN_mod_exp(Xbar, old_X_value, alpha, pm, ctx))
               throw SSL_ERROR;
            if (!BN_mod_exp(Ybar, old_Y_value, alpha, pm, ctx))
               throw SSL_ERROR;
            X_node->erase_all_characters();
            add_BN_characters(X_node, Xbar, DEC);
            Y_node->erase_all_characters();
            add_BN_characters(Y_node, Ybar, DEC);
         }
         // Copy the modified voted ballot into the RawBallotBox
         root_rbb->add_element(current_rvb->deep_copy());
      }
      std::ostringstream oss; // A stream to hold xml_pvcb
      oss << xml_pvcb;
      *pre_vcode_box = VHTI_dup(oss.str().c_str());
   }
   catch (const VHUtil::Exception & e) {
      VHTI_set_last_error(e);
      result = e.getResultNo();
   }
   return result;
}
