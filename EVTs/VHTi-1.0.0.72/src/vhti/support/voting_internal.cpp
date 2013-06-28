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

#include <support/voting_internal.h>
#include <support/internal_error.h>
#include "vhti/random.h"
#include <util/xml_tree.h>
#include <util/vh_excpt.h>

#include <string>
#include <sstream>
int
get_bsn_random_bits (RandomState random_state,
                     RandomBits * random_bits_out,
                     RandomState * random_state_out)
{
   int result = 0;
   *random_bits_out = NULL;
   *random_state_out = NULL;

   try
   {
      int num_bits = 32;
      auto_freeing <RandomState> return_random_state = 0;
      auto_freeing <RandomBits> newbits = 0;
      VH_propagate (VHTI_get_bits(random_state, num_bits,
         &return_random_state, &newbits),
         GEN_VCK_GET_BITS);
      *random_state_out = VHTI_dup(return_random_state);
      *random_bits_out = VHTI_dup(newbits);
   }
   catch (const VHUtil::Exception & e)
   {
      VHTI_set_last_error(e);
      result = e.getResultNo();
   }
   return result;
}
