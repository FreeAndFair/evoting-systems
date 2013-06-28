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

#include "vhti/gen_seccoeff.h"
#include "vhti/keyshare_util.h"
#include <support/internal_error.h>
#include <support/bignum.h>
#include <support/xml_tree_group_check.h>
#include <keyshare/keyshare_internal.h>
#include <support/random_internal.h>
#include <misc/xml_tree.h>
#include <string>
#include <sstream>

int
VHTI_generate_secret_coefficients (KeyGenParameters key_gen_parameters,
                                   Authority authority,
                                   RandomState random_state,
                                   SecretCoefficients *secret_coefficients,
                                   RandomState * random_state_out)
{
   // Assume success until told otherwise
   int result = 0;
   *secret_coefficients = NULL;
   *random_state_out = NULL;
   // The Election Modulus
   auto_BN pm;
   // The Election Subgroup Modulus
   auto_BN qm;
   // The Election Subgroup Generator
   auto_BN gen;
   // The Election Public Key
   auto_BN ePublicKey;
   // The number of authorities
   int na = 0;
   // The threshold number of authorities needed for tabulation
   int th = 0;
   
   try
   {
      result = (::VHTI_validate(KEY_GEN_PARAMETERS, key_gen_parameters)
                || ::VHTI_validate(AUTHORITY, authority)
                || ::VHTI_validate(RANDOM_STATE, random_state));

      if (result != 0) throw VH_exception("VALIDATION_FAILURE");

      VHInternal::get_keygen_parameters (key_gen_parameters, pm, qm, gen,
                                         na, th);

      // Create a RandomState object
      VHInternal::RS rs (random_state);

      // The AuthFingerprint
      const std::string aid = (VHUtil::xml_tree_group_check (authority, pm, qm, gen, ePublicKey))
         .root ()->attribute(AUTH_FINGERPRINT);
      
      // Add attribute AuthFingerprint to SecretCoefficients
      // An empty xml tree to hold SecretCoefficients
      VHUtil::xml_tree xml_sc("<" SECRET_COEFFICIENTS "/>");
      xml_sc.root ()->add_attribute(AUTH_FINGERPRINT, aid.c_str());
      
      // Generate th number of elements in q and insert
      // them as SmallTheta elements into SecretCoefficients
      
      for (int i=0; i<th; i++)
      {
         // The values of small theta
         auto_BN smtheta;

         VHInternal::rand_range2(BN_value_one(),
                                 qm,
                                 rs,
                                 smtheta);
         // A stream to hold the order attribute
         std::ostringstream oss;
         oss << i;  // this is the Order
         // A node for small theta       
         add_BN_element(xml_sc.root (),
                        SMALL_THETA, smtheta)->add_attribute(ORDER, oss.str().c_str());
      }

      *secret_coefficients = VHTI_dup(xml_sc.str().c_str());
      *random_state_out = VHTI_dup (rs);
   }
   catch (const VHUtil::Exception & e)
   {
      VHTI_set_last_error(e);
      result = e.getResultNo();
   }
   
   return result;
}
