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

#include "vhti/gen_vvdict.h"
#include "voting/voting_internal.h"
#include "vhti/gen_verification_code.h"
#include <support/internal_error.h>
#include <support/bignum.h>
#include <support/sanity.h>
#include <support/xml_tree_group_check.h>
#include <misc/xml_tree.h>
#include <string>
#include <sstream>

int
VHTI_generate_vote_verification_dictionary
    (VoteVerificationKeys vv_keys,
     BlankBallot blank_ballot,
     BallotSequenceNumber bsn,
     int vv_len,
     AlphabetEncoding vv_alphabet,
     VoteVerificationDictionary * vv_dictionary)
{
   // Assume success until told otherwise
   int result = 0;
   *vv_dictionary = NULL;
   auto_BN pm(NULL); // The Election Modulus
   auto_BN qm(NULL); // The Election Subgroup Modulus
   auto_BN gen(NULL); // The Election Subgroup Generator
   auto_BN ePublicKey(NULL); // The Election Public Key
   
   try
   {
      result = (::VHTI_validate(VOTE_VERIFICATION_KEYS, vv_keys)
         || ::VHTI_validate(BLANK_BALLOT, blank_ballot)
         || ::VHTI_validate(BALLOT_SEQUENCE_NUMBER, bsn)
         || ::VHTI_validate(ALPHABET_ENCODING, vv_alphabet));
      
      if (result != 0) throw VH_exception("VALIDATION_FAILURE");
      
      // An xml tree from the blank_ballot input
      VHUtil::xml_tree_group_check xml_bb(blank_ballot, pm, qm, gen, ePublicKey);
      VHUtil::xml_node root_bb = xml_bb.root(); // The root node of xml_bb

      VHInternal::sanity_check_blank_ballot (root_bb);
      
      // An xml tree from the vv_keys input
      VHUtil::xml_tree_group_check xml_vvkeys(vv_keys, pm, qm, gen, ePublicKey);
      VHUtil::xml_node root_vv_keys = xml_vvkeys.root(); // The root node of xml_vvkeys
      
      // An xml tree from the bsn input
      VHUtil::xml_tree_group_check xml_bsn(bsn, pm, qm, gen, ePublicKey);
      VHUtil::xml_node root_bsn = xml_bsn.root(); // The root node of xml_bsn

      // An xml tree from the vv_alphabet input
      VHUtil::xml_tree_group_check xml_vv_alphabet(vv_alphabet, pm, qm, gen, ePublicKey);
      std::string str_vv_alphabet(vv_alphabet); // A string from vv_alphabet

      auto_freeing < VoteVerificationDictionary > internal_vv_dictionary = 0;
      VHInternal::generate_vote_verification_dictionary(
         root_vv_keys, root_bb, root_bsn, vv_len, str_vv_alphabet,
         &internal_vv_dictionary);

      *vv_dictionary = VHTI_dup(internal_vv_dictionary);
   }
   catch (const VHUtil::Exception & e)
   {
      VHTI_set_last_error(e);
      result = e.getResultNo();
   }
   return result;
}
