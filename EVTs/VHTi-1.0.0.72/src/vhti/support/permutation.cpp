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

#include "vhti/permutation.h"
#include "vhti/random.h"
#include <support/random_internal.h>
#include <support/internal_error.h>
#include <support/bignum.h>
#include <misc/xml_tree.h>
#include <misc/vh_excpt.h>

#include <string>
#include <sstream>
#include <map>

// return a permutation of the integers from 1 to nsize, inclusive.
int
VHTI_get_permutation(RandomState random_state,
                     int nsize,
                     Permutation * perm,
                     RandomState * random_state_out)
{
   int result = 0;
   *perm = NULL;
   *random_state_out = NULL;
   std::map< auto_BN, int > pmap;

   try
   {
      VHInternal::RS rs (random_state);

      // Make a Permutation container
      VHUtil::xml_tree xml_perm("<" PERMUTATION "/>");
      VHUtil::xml_node root_perm = xml_perm.root();
      std::ostringstream oss;
      oss << nsize;
      root_perm->add_attribute(PERMUTATION_SIZE, oss.str());

      // Calculate how many bits to ask for: Function k(n)
      // Get log2n + 10 or 20 (pick max)
      int log_value = 0;

      {
         int ncopy = nsize;
         while (ncopy = ncopy>>1)
         {
            log_value++;
         }
      }

      const int k_of_n=max(log_value + 10, 20);

      int i = 1;
      while (i <= nsize)
      {
         auto_freeing<RandomBits> random_bits = 0;
         auto_freeing<RandomState> return_random_state = 0;

         VH_propagate(VHTI_get_bits(rs, k_of_n,
                                    rs, &random_bits), PERMUTATION_GET_BITS);

         std::string str_random_bits(random_bits);
         VHUtil::xml_tree xml_bits(str_random_bits);
         VHUtil::xml_node root_bits = xml_bits.root();
         auto_BN bn_bits;
         bn_bits = xml2BN(root_bits);
         pmap.insert(std::pair< auto_BN, int >(bn_bits, i));
         i++;
      }

      // When we are done, we pick out the map elements and put them into
      // the Permutation structure
      std::ostringstream perm_oss;
      std::map< auto_BN, int >::iterator it;
      it = pmap.begin();
      while (it != pmap.end())
      {
         int data = it->second;
         perm_oss << data;
         it++;
         perm_oss << " ";
      }

      // When you have the string built up,
      // you can stick it in the Permutation XML
      root_perm->add_characters(perm_oss.str());
      std::ostringstream final_oss;
      final_oss << xml_perm;
      *perm = VHTI_dup(final_oss.str().c_str());
      *random_state_out = VHTI_dup (rs);
   }
   catch (const VHUtil::Exception & e)
   {
      VHTI_set_last_error(e);
      result = e.getResultNo();
   }
   return result;
}
