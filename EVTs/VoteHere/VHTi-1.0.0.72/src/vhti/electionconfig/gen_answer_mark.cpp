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

#include <vhti/gen_answer_mark.h>
#include <support/internal_error.h>
#include <support/random_internal.h>
#include <support/support_internal.h>
#include <support/xml_tree_group_check.h>
#include <support/bignum.h>
#include <misc/xml_tree.h>
#include "pki/misc.h"           // for SSL_ERROR

#include <string>
#include <sstream>

int
VHTI_generate_answer_mark (CryptoGroupParameters crypto_group_parameters,
                           AlphabetEncoding encoding,
                           RandomState random_state,
                           AnswerMark *answer_mark,
                           RandomState * ending_random_state)
{
   int result = 0; // Assume success until told otherwise
   auto_BN pm(NULL); // The Election Modulus
   auto_BN qm(NULL); // The Election Subgroup Modulus
   auto_BN gen(NULL); // The Election Subgroup Generator.  Ignored.
   auto_BN ePublicKey(NULL); // The Election Public Key.  Ignored.

   *answer_mark = NULL;
   *ending_random_state = NULL;

   try {
      VH_zero (::VHTI_validate (CRYPTO_GROUP_PARAMETERS, crypto_group_parameters), VALIDATION_FAILURE);
      VH_zero (::VHTI_validate (ALPHABET_ENCODING, encoding)                     , VALIDATION_FAILURE);
      VH_zero (::VHTI_validate (RANDOM_STATE, random_state)                      , VALIDATION_FAILURE);

      VHInternal::RS rs (random_state); // A RandomState object
      // An xml tree from the crypto_group_parameters input
      VHUtil::xml_tree_group_check cgp (crypto_group_parameters, pm, qm, gen, ePublicKey);
      
      // This is the same  value we encountered when we generated p
      // and q in the first place.  There it was called "r".
      auto_BN p_minus_1_over_q;
      // A random BIGNUM in Zp
      auto_BN random_Z_p;
      // The answer mark
      auto_BN am;

      // An OpenSSL structure that holds BIGNUM temporary variables
      // used by library functions
      auto_BN_CTX ctx(BN_CTX_new());
      VH_nonzero (ctx, BN_CTX_NEW);

      // p - 1
      auto_BN bn_one_less_than_p;
      VH_nonzero (BN_sub(bn_one_less_than_p, pm, BN_value_one())                , BN_SUB);
      VH_nonzero (BN_div(p_minus_1_over_q, NULL, bn_one_less_than_p, qm, ctx)   , BN_DIV);
      
      // 0 and 1 make lousy answer marks
      while (BN_is_zero(am)
             ||
             BN_is_one(am))
      {
         // Pick a random element of Z_p*
         VHInternal::rand_range2 (BN_value_one (), pm, rs,
                                  random_Z_p);
      
         // Raise random_Z_p to the power of "r", yielding an element of
         // the order q subgroup. 

         VHInternal::fixed_mod_exp (am, random_Z_p, p_minus_1_over_q, pm, ctx);
      }

      // An xml tree to hold the AnswerMark
      VHUtil::xml_tree xml_am ("<" ANSWER_MARK "/>");

      add_BN_characters(xml_am.root (), am, encoding);

      *answer_mark = VHTI_dup(xml_am.str().c_str());
      *ending_random_state = VHTI_dup (rs);
   }
   catch (const VHUtil::Exception & e) {
      VHTI_set_last_error(e);
      result = e.getResultNo();
   }
   return result;
}
