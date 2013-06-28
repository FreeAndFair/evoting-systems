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

#include "vhti/gen_vvdict_comm.h"
#include "vhti/sign.h"
#include <support/internal_error.h>
#include <support/random_internal.h>
#include <support/support_internal.h>
#include <support/bignum.h>
#include <support/xml_tree_group_check.h>
#include <support/sanity.h>
#include <misc/xml_tree.h>
#include <misc/safe_xml_tree.h>
#include <string>
#include <sstream>

int
VHTI_generate_vvdict_commits (Authority authority,
                              GeneralPurposePrivateKey private_signature_key,
                              VoteVerificationKey prn_seed,
                              BlankBallot blank_ballot,
                              BallotSequenceNumbers bsns,
                              SignedTrusteeDictionaryCommitments *trustee_dict_comm)
{
   int result = 0; // Assume success until told otherwise
   auto_BN pm(NULL); // The Election Modulus
   auto_BN qm(NULL); // The Election Subgroup Modulus
   auto_BN gen(NULL); // The Election Subgroup Generator
   auto_BN ePublicKey(NULL); // The Election Public Key
   // An OpenSSL structure that holds BIGNUM temporary variables used by
   // library functions
   auto_BN_CTX ctx(BN_CTX_new());
   *trustee_dict_comm = NULL;
   
   try
   {
      VH_nonzero (ctx, BN_CTX_NEW);

      VH_zero (::VHTI_validate(AUTHORITY, authority),
               VALIDATION_FAILURE);
      VH_zero (::VHTI_validate(GENERAL_PURPOSE_PRIVATE_KEY,
                               private_signature_key),
               VALIDATION_FAILURE);
      VH_zero (::VHTI_validate(VOTE_VERIFICATION_KEY, prn_seed),
               VALIDATION_FAILURE);
      VH_zero (::VHTI_validate(BLANK_BALLOT, blank_ballot),
               VALIDATION_FAILURE);
      VH_zero (::VHTI_validate(BALLOT_SEQUENCE_NUMBERS, bsns),
               VALIDATION_FAILURE);

      // An xml tree from the blank_ballot input
      VHUtil::xml_tree_group_check xml_bb(blank_ballot, pm, qm, gen, ePublicKey);
      VHInternal::sanity_check_blank_ballot (xml_bb.root ());

      // An xml tree from the authority input
      VHUtil::xml_tree_group_check xml_auth(authority, pm, qm, gen, ePublicKey);

      // Make tree out of BSNs
      VHUtil::xml_tree_group_check xml_bsns(bsns, pm, qm, gen, ePublicKey);

      // An xml tree with the prn_seed input
      VHUtil::xml_tree_group_check xml_seed(prn_seed, pm, qm, gen, ePublicKey);

      // Find out how many questions per ballot
      // Put the QuestionRef in a vector for easy access
      std::vector< auto_BN > question_vec;
      for (int i=0; i<xml_bb.root ()->element_count(); i++)
      {
         // The current element of the blank ballot xml
         VHUtil::xml_node current_bb_node = xml_bb.root ()->e(i);
         if (current_bb_node->name() == BALLOT_QUESTION)
         {
            // A string with the QuestionReference
            std::string question_ref(current_bb_node->attribute(QUESTION_REFERENCE));
            // Turn it into an auto_BN for use later
            auto_BN qref_bn = BN_bin2bn((unsigned char *)question_ref.c_str(),
                                        question_ref.size(), 0);
            VH_nonzero (qref_bn, BN_BIN2BN);
            question_vec.push_back(qref_bn);
         }
      }
      
      // Seed a RandomIJState with the VoteVerificationKey
      // First build up a RandomIJState object
      VHUtil::xml_tree xml_rij_state("<" RANDOM_IJ_STATE "/>");

      xml_rij_state.root ()->add_attribute(SOURCE_TYPE, VHInternal::SourceType);
      // An xml tree to hold a RandomSeedKey
      VHUtil::xml_tree xml_key("<" RANDOM_SEED_KEY "/>");

      xml_key.root ()->add_characters(xml_seed.root ()->characters());
      xml_rij_state.root ()->add_element(xml_key.root ()->deep_copy());

      // An empty xml tree to hold the TrusteeDictionaryCommitments
      VHUtil::xml_tree xml_tdc("<" TRUSTEE_DICTIONARY_COMMITMENTS "/>");

      // Add in the authority and the blank ballot
      xml_tdc.root ()->add_element(xml_auth.root ()->deep_copy());
      xml_tdc.root ()->add_element(xml_bb.root ()->deep_copy());

      // Get a random alpha_ij in Zq*, i is the bsn and j is the QuestionRef
      auto_freeing <RandomState> return_random_state = 0;
      for (int num_bsn=0; num_bsn<xml_bsns.root ()->element_count(); num_bsn++)
      {
         // A node to hold the BSNDictionaryCommitments
         VHUtil::xml_node root_bsn_comms =
            xml_tdc.root ()->new_element(BSN_DICTIONARY_COMMITMENTS);
         // The current bsn
         VHUtil::xml_node current_bsn = xml_bsns.root ()->e(num_bsn);
         root_bsn_comms->add_element(current_bsn->deep_copy());

         for (int num_q=0; num_q<question_vec.size(); num_q++)
         {
            auto_BN alpha; // Our exponent
            VHInternal::rand_range_2ij (BN_value_one (),
                                        qm,
                                        xml2BN(current_bsn),
                                        question_vec[num_q],
                                        xml_rij_state.str().c_str(),
                                        &return_random_state,
                                        alpha);
            // Don't use the return_random_state because we want the same one
            
            auto_BN bsn_comm; // The commitment
            VHInternal::fixed_mod_exp(bsn_comm, gen, alpha,
                                      pm, ctx);
            add_BN_element(root_bsn_comms, DICTIONARY_COMMITMENT,
                           bsn_comm, DEC);
         }
      }

      VH_propagate (VHTI_sign_xml (private_signature_key, xml_tdc.str ().c_str (),
                                   trustee_dict_comm), "SIGNING_XML");
   }
   catch (const VHUtil::Exception & e)
   {
      VHTI_set_last_error(e);
      result = e.getResultNo();
   }
   return result;
}
