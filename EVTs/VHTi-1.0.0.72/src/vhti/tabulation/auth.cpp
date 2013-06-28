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

#include "vhti/auth.h"
#include <support/internal_error.h>
#include <support/sanity.h>
#include <misc/vh_excpt.h>
#include <misc/xml_tree.h>
#include <misc/safe_xml_tree.h>
#include <string>
#include <sstream>

int
VHTI_authenticate(SignedVotedBallots signed_voted_ballots,
                  VoterRoll voter_roll,
                  BlankBallot blank_ballot,
                  RawBallotBox *raw_ballot_box)
{
   * raw_ballot_box = NULL;
   // Assume success until told otherwise
   int result = 0;
   
   try
   {
      result = 
         (::VHTI_validate(SIGNED_VOTED_BALLOTS, signed_voted_ballots)
          || ::VHTI_validate(VOTER_ROLL, voter_roll)
          || ::VHTI_validate(BLANK_BALLOT, blank_ballot));

      if (result != 0) throw VH_exception("VALIDATION_FAILURE");
      
      VHInternal::sanity_check_blank_ballot (VHUtil::xml_tree (blank_ballot).root ());
      
      // The voter roll, parsed
      VHUtil::xml_tree voter_roll_tree (voter_roll);

      // An xml tree from the signed_voted_ballots input
      VHUtil::xml_tree xml_svbs(signed_voted_ballots);
      // An empty xml tree for the RawBallotBox we will create
      VHUtil::xml_tree xml_rbb("<" RAW_BALLOT_BOX "/>");
      
      // The root node of xml_xvbs
      VHUtil::xml_node svbs = xml_svbs.root();
      // The root node of xml_rbb
      VHUtil::xml_node rbb = xml_rbb.root();
      // A node for a voted ballot
      VHUtil::xml_node vb = NULL;
      
      // The number of signed voted ballots passed as input
      int num_svb_elems = svbs->element_count();
      for (int j=0; j<num_svb_elems; j++)
      {
         // The current signed voted ballot
         std::ostringstream svb_stream;
         svb_stream << *(svbs->e(j));
         
         // The corresponding public key
         std::ostringstream pubkey_stream;
         pubkey_stream << *(voter_roll_tree.root ()->e (j)->e (GENERAL_PURPOSE_PUBLIC_KEY));
         VHUtil::safe_xml_tree vb_tree (svb_stream.str (), VOTED_BALLOT, pubkey_stream.str ());

         rbb->add_element(vb_tree.root ()->e(RAW_VOTED_BALLOT)->deep_copy());
      }
      
      // A stream to contain the raw ballot box
      std::ostringstream rbb_stream;
      rbb_stream << xml_rbb;
      * raw_ballot_box = VHTI_dup(rbb_stream.str().c_str());
   }
   catch (const VHUtil::Exception & e) {
      VHTI_set_last_error(e);
      result = e.getResultNo();
   }

   return result;
}
