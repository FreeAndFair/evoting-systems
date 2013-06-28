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

#include "vhti/gen_vvkey.h"
#include "vhti/random.h"
#include <support/internal_error.h>
#include <support/bignum.h>
#include <misc/xml_tree.h>
#include <string>
#include <sstream>

int
VHTI_generate_vvk (RandomState random_state,
                   VoteVerificationKey * vv_key,
                   RandomState *random_state_out)
{
   int result = 0;
   *vv_key = NULL;
   *random_state_out = NULL;
   
   try
   {
      result = ::VHTI_validate(RANDOM_STATE, random_state);
      
      if (result != 0) throw VH_exception("VALIDATION_FAILURE");

      // The new RandomState
      auto_freeing <RandomState> return_random_state = 0;
      // The RandomBits
      auto_freeing <RandomBits> newbits = 0;
      VH_propagate (VHTI_get_bits(random_state, VHInternal::digest_bits,
         &return_random_state, &newbits),
         GEN_VCK_GET_BITS);
      *random_state_out = VHTI_dup(return_random_state);
      
      std::string str_bits(newbits); // A string with the newbits
      VHUtil::xml_tree xml_bits(str_bits); // An xml tree with str_bits
      VHUtil::xml_node root_bits = xml_bits.root(); // The root node of xml_bits
      // An empty xml tree to hold the VoteVerificationKey
      VHUtil::xml_tree xml_vvk("<" VOTE_VERIFICATION_KEY "/>");
      // The root node of xml_vvk
      VHUtil::xml_node root_vvk = xml_vvk.root();
      root_vvk->add_characters(root_bits->characters());
      // A stream to hold xml_vvk
      std::ostringstream vvk_stream;
      vvk_stream << xml_vvk;
      *vv_key = VHTI_dup(vvk_stream.str().c_str());
   }
   catch (const VHUtil::Exception & e)
   {
      VHTI_set_last_error(e);
      result = e.getResultNo();
   }
   return result;
}

