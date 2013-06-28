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

#include "vhti/check_vc_pds_and_combine.h"
#include "vhti/check_pds_and_combine.h"
#include "misc/xml_tree.h"
#include "misc/safe_xml_tree.h"
#include "util/sslerror.h"
#include <tabulation/tabulation_internal.h>
#include <support/internal_error.h>
#include <support/xml_tree_group_check.h>
#include <support/support_internal.h>
#include <string.h>
#include <sstream>

int
VHTI_check_vcode_partial_decrypts_and_combine
   (PreVerificationCodeBoxes pre_vcode_boxes,
    AuthorityPartialDecrypts auth_partial_decrypts,
    SignedVotedBallots signed_voted_ballots,
    SignedBlankBallot signed_blank_ballot,
    GeneralPurposePublicKey ballot_signing_key,
    int v_len,
    AlphabetEncoding v_alphabet,
    VoteVerificationStatements *verification_statements,
    const char **combine_partial_decrypt_result)
{
   int result = 0; // Assume success until told otherwise

   *verification_statements = NULL;
   *combine_partial_decrypt_result = NULL;

   auto_BN pm(NULL); // The Election Modulus
   auto_BN qm(NULL); // The Election Subgroup Modulus
   auto_BN gen(NULL); // The Election Subgroup Generator
   auto_BN ePublicKey(NULL); // The Election Public Key
   
   try
   {
      result = (::VHTI_validate(PRE_VERIFICATION_CODE_BOXES, pre_vcode_boxes)
         || ::VHTI_validate(AUTHORITY_PARTIAL_DECRYPTS, auth_partial_decrypts)
         || ::VHTI_validate(SIGNED_VOTED_BALLOTS, signed_voted_ballots)
         || ::VHTI_validate(SIGNED_BLANK_BALLOT, signed_blank_ballot)
         || ::VHTI_validate(ALPHABET_ENCODING, v_alphabet));

      if (result != 0) throw VH_exception("VALIDATION_FAILURE");
      
      VH_nonzero (v_len <= VHInternal::digest_bits, V_LEN_LONGER_THAN_DIGEST_LENGTH);
      
      // An empty xml tree to hold the PartiallyDecryptedBallotBox
      VHUtil::xml_tree xml_pdbb("<" PARTIALLY_DECRYPTED_BALLOT_BOX "/>");
      // The root node of xml_pdbb
      VHUtil::xml_node root_pdbb = xml_pdbb.root();

      // An xml tree from the signed_blank_ballot input
      VHUtil::xml_tree_group_check xml_bb(signed_blank_ballot,
                                           BLANK_BALLOT,
                                           ballot_signing_key,
                                           pm, qm, gen, ePublicKey);
      // Check the pre_vcode_boxes input
      VHUtil::xml_tree_group_check xml_pvb(pre_vcode_boxes, pm, qm, gen, ePublicKey);
      
      // Send the PreVerificationCodeBoxes to get multiplied together
      // The returning raw_ballot_box
      auto_freeing < RawBallotBox > verification_raw_ballot_box = 0;
      VHInternal::combine_pre_vv_results
         (pre_vcode_boxes,
          xml_bb, &verification_raw_ballot_box);
      
      // A string from the verification_raw_ballot_box
      std::string str_rbb(verification_raw_ballot_box);
      VHUtil::xml_tree xml_rbb(str_rbb); // An xml tree from str_rbb
      VHUtil::xml_node root_rbb = xml_rbb.root(); // The root node of xml_rbb
      root_pdbb->add_element(root_rbb->deep_copy());
      
      // Add in the AuthorityPartialDecrypt
      VHUtil::xml_tree_group_check xml_apds(auth_partial_decrypts, pm, qm, gen, ePublicKey);
      VHUtil::xml_node root_apds = xml_apds.root(); // The root node of xml_apds
      root_pdbb->add_element(root_apds->deep_copy());
      
      // Returning raw clear text ballots from check_partial_decrypts_and_combine
      auto_freeing<RawClearTextBallots> raw_ctbs = 0;
      // The returning results from check_partial_decrypts_and_combin
      auto_freeing<Results> combine_partial_decrypt_res = 0;
      // A stream to hold xml_pdbb
      std::ostringstream pdbb_stream;
      pdbb_stream << xml_pdbb;
      
      VHInternal::check_partial_decrypts_and_combine
         (signed_blank_ballot, ballot_signing_key,
          pdbb_stream.str().c_str(), &raw_ctbs,
          &combine_partial_decrypt_res);
      
      // An empty xml tree for the VoteVerificationStatements
      VHUtil::xml_tree xml_vv_statements("<" VOTE_VERIFICATION_STATEMENTS "/>");
      // The root node of xml_vv_statements
      VHUtil::xml_node root_vv_statements = xml_vv_statements.root();
      // An xml tree from the signed_voted_ballots input
      VHUtil::xml_tree_group_check xml_svbs(signed_voted_ballots, pm, qm, gen, ePublicKey);

      *combine_partial_decrypt_result =
         VHTI_dup(combine_partial_decrypt_res);
      
      // A string from the raw clear text ballots
      std::string str_raw_ctbs(raw_ctbs);
      // An xml tree from str_raw_ctbs
      VHUtil::xml_tree xml_raw_ctbs(str_raw_ctbs);
      // The root node of xml_raw_ctbs
      VHUtil::xml_node root_raw_ctbs = xml_raw_ctbs.root();

      for (int num_raw_ctb=0;
           num_raw_ctb<root_raw_ctbs->element_count();
           num_raw_ctb++)
      {
         // A node to hold a single VoteVerificationStatement
         VHUtil::xml_node root_vvs =
            root_vv_statements->new_element(VOTE_VERIFICATION_STATEMENT);
         // The current SignedVotedBallot
         std::ostringstream tmp;
         tmp << *(xml_svbs.root ()->element(num_raw_ctb));
         VHUtil::safe_xml_tree current_svb (tmp.str (), VOTED_BALLOT, "NO_SIGNATURE_CHECK") ;
         // The current BallotSequenceNumber
         VHUtil::xml_node current_bsn =
            current_svb.root ()->e(BALLOT_SEQUENCE_NUMBER);
         root_vvs->add_element(current_bsn->deep_copy());
         
         // The current RawClearTextBallot
         VHUtil::xml_node current_raw_ctb = root_raw_ctbs->
            e(num_raw_ctb);
         for (int i=0; i<current_raw_ctb->element_count(); i++)
         {
            // The current answer mark
            auto_BN bn_am = xml2BN(current_raw_ctb->e(i));
            // An array of BIGNUMs to be hashed
            const BIGNUM * arr[] = {bn_am};
            // The hash value
            auto_BN hashval = GetHashOfNBNs(arr, sizeof(arr) / sizeof(arr[0]));
            // The verification code
            auto_BN bn_vcode;
            if (!BN_rshift(bn_vcode, hashval, (VHInternal::digest_bits - v_len)))
               throw SSL_ERROR;

            // Get the current QuestionReference to put as an attribute to the
            // VoteVerificationCode
            std::string current_qref = xml_bb.root()->
               e(BALLOT_QUESTION, i)->attribute(QUESTION_REFERENCE);
            
            // An xml node for the VoteVerificationCode
            VHUtil::xml_node root_vvc
               = root_vvs->new_element(VOTE_VERIFICATION_CODE);
            add_BN_characters(root_vvc, bn_vcode, v_alphabet);
            root_vvc->add_attribute(QUESTION_REFERENCE, current_qref);
         }
      }

      *verification_statements = VHTI_dup(xml_vv_statements.str().c_str());

#if defined (MOD_EXP_STATS)
      dump_stats();
#endif
   }
   catch (const VHUtil::Exception & e)
   {
      VHTI_set_last_error(e);
      result = e.getResultNo();
   }
   return result;
}
