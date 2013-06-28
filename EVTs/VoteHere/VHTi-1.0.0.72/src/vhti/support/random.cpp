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

#include "vhti/random.h"
#include <support/random_internal.h>
#include <support/internal_error.h>
#include <support/bignum.h>
#include <misc/xml_tree.h>
#include <misc/vh_excpt.h>
#include <util/sslerror.h>
#include <limits.h>

#include <cassert>
#include <string>
#include <sstream>
#include <iostream>

int
VHTI_generate_random_state(RandomSeedKey key,
                           RandomState * random_state)
{
   int result = 0;
   *random_state = NULL;
   
   try
   {
      VH_propagate(VHTI_validate(RANDOM_SEED_KEY, key), GENERATE_RANDOM_STATE);

      // Get key
      VHUtil::xml_tree xml_key(key);
      VHUtil::xml_node root_key = xml_key.root();
      std::string key_data = root_key->characters();
         
      auto_BN key_bn =
         BN_bin2bn((unsigned char *)key_data.c_str(), key_data.size(), 0);
      if (!key_bn)
         throw SSL_ERROR;

      // get hash of key
      const BIGNUM * arr[] = {key_bn};
      auto_BN hashval;
      hashval = GetHashOfNBNs(arr, sizeof(arr) / sizeof(arr[0]));
         
      // build up new state object to pass to GetBits
      VHUtil::xml_tree xml_rstate_bar("<" RANDOM_STATE "/>");

      xml_rstate_bar.root()->add_element(root_key->deep_copy());
      add_BN_element(xml_rstate_bar.root(), RANDOM_BLOCK, hashval, DEC);
      xml_rstate_bar.root()->add_attribute(SOURCE_TYPE, VHInternal::SourceType);

      *random_state = VHTI_dup(xml_rstate_bar.str().c_str());
   }
   catch (const VHUtil::Exception & e)
   {
      VHTI_set_last_error(e);
      result = e.getResultNo();
   }
   return result;
}

int
VHTI_get_bits(RandomState random_state,
              int needed_bits,
              RandomState * return_random_state,
              RandomBits * bits)
{
   int result = 0;
   *return_random_state = NULL;
   *bits = NULL;

   try {
      result = ::VHTI_validate(RANDOM_STATE, random_state);
      if (!result)
      {
         VHInternal::RS rs (random_state);
         *bits = rs.get_bits (needed_bits);
         *return_random_state = VHTI_dup (rs);
      }
   }
   catch (const VHUtil::Exception & e) {
      VHTI_set_last_error(e);
      result = e.getResultNo();
   }
   return result;
}
