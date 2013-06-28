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

#include "vhti/gen_broadcast.h"
#include "vhti/keyshare_util.h"
#include <support/internal_error.h>
#include <support/bignum.h>
#include <keyshare/keyshare_internal.h>
#include <support/random_internal.h>
#include <support/support_internal.h>
#include <support/xml_tree_group_check.h>
#include <misc/xml_tree.h>

#include <math.h>
#include <string>
#include <sstream>

int
VHTI_generate_broadcast (KeyGenParameters key_gen_parameters,
                         SecretCoefficients secret_coefficients,
                         RandomState random_state,
                         BroadcastValue *broadcast_value,
                         RandomState *random_state_out)
{
   // Assume success until told otherwise
   int result = 0;
   *broadcast_value = NULL;
   *random_state_out = NULL;
   // The Election Modulus
   auto_BN pm(NULL);
   // The Election Subgroup Modulus
   auto_BN qm(NULL);
   // The Election Subgroup Generator
   auto_BN gen(NULL);
   // The Election Public Key
   auto_BN ePublicKey(NULL);
   // The number of authorities
   int na = 0;
   // The threshold number of authorities needed for tabulation
   int th = 0;
   // An OpenSSL structure that holds BIGNUM temporary variables
   // used by library functions
   auto_BN_CTX ctx(BN_CTX_new());
   
   try
   {
      VH_nonzero (ctx, BN_CTX_NEW);
      result = (::VHTI_validate(KEY_GEN_PARAMETERS, key_gen_parameters)
         || ::VHTI_validate(SECRET_COEFFICIENTS, secret_coefficients)
         || ::VHTI_validate(RANDOM_STATE, random_state));

      if (result != 0) throw VH_exception("VALIDATION_FAILURE");

      // Get ElectionModulus, ElectionSubgroupModulus,
      // ElectionSubgroupGenerator, and Threshold values
      // from key_gen_parameters
      VHInternal::get_keygen_parameters (key_gen_parameters, pm, qm, gen,
         na, th);

      // Create a RandomState object
      VHInternal::RS rs (random_state);
      // An xml tree or the individual authority's BVs
      VHUtil::xml_tree xml_bv("<" BROADCAST_VALUE "/>");

      // An xml tree from the secret_coefficients input
      VHUtil::xml_tree_group_check xml_sc(secret_coefficients, pm, qm, gen, ePublicKey);
      VHInternal::sanity_check_orders (th,
                                       xml_sc);

      // Carry the attribute AuthCertFingerprint from the SecretCoefficients
      // into BroadcastValues

      xml_bv.root ()->add_attribute (AUTH_FINGERPRINT,
                                     xml_sc.root ()->attribute(AUTH_FINGERPRINT));
      
      // Extract secret coefficients, pay attention to attribute Order
      // Raise ElectionSubgroupGenerator to the power of each coefficient
      // and insert them as BigTheta elements into BroadcastValues, 
      // keeping the Order consistent
      auto_BN smtht_order0;  // save these off to be used to calculate "s"
      auto_BN bigtht_order0; // The Theta of order 0

      for (int i = 0; i < th; i++)
      {
         // The current coefficient
         auto_BN smtheta = xml2BN(xml_sc.root ()->e(i));

         // The broadcast value
         auto_BN bigtheta;
         VH_nonzero (BN_mod_exp( bigtheta, gen, smtheta, pm, ctx), BN_MOD_EXP);
         const std::string this_order = xml_sc.root ()->e(i)->attribute(ORDER);

         if (0 == VHInternal::int_from_attribute (xml_sc.root ()->e(i), ORDER))
         {
            smtht_order0 = smtheta;
            bigtht_order0 = bigtheta;
         }

         // Add a node to the BroadcastValues with the Theta

         add_BN_element (xml_bv.root (),
                         BIG_THETA,
                         bigtheta)
            ->add_attribute(ORDER, this_order);
      }
      
      // Generate a random number (omega) in the order-q subgroup.  We
      // do this by first choosing log_omega such that 1<= log_omega <
      // q, then computing omega = g^log_omega.
      auto_BN log_omega(NULL);
      // An auto_BN with the value of 1
      auto_BN one_bn;
      VH_nonzero (BN_one(one_bn), BN_ONE);
      
      VHInternal::rand_range2 (one_bn, qm, rs, log_omega);
      
      auto_BN omega;
      VH_nonzero (BN_mod_exp(omega, gen, log_omega, pm, ctx), BN_MOD_EXP);
      add_BN_element(xml_bv.root (), OMEGA, omega);
      
      // Get a Hash of theta0 and omega
      auto_BN hashval;
      // The hash value before doing a modulus
      auto_BN tmp_hash = GetHashOf2BNs(bigtht_order0, omega);
      VH_nonzero (BN_mod(hashval, tmp_hash, qm, ctx), BN_MOD);
      
      // Solve for "s" (something) = (log_omega+(smtht_order0*hashval))
      auto_BN tmp_mul;
      // The value of s
      auto_BN s_value;
      VH_nonzero (BN_mod_mul(tmp_mul, smtht_order0, hashval, qm, ctx),
                  BN_MOD_MUL);
      VH_nonzero (BN_add(s_value, tmp_mul, log_omega), BN_ADD);
      s_value.Canonicalize(qm);
      add_BN_element(xml_bv.root (), SOMETHING, s_value);

      *broadcast_value = VHTI_dup(xml_bv.str().c_str());
      *random_state_out = VHTI_dup (rs);
   }
   catch (const VHUtil::Exception & e)
   {
      VHTI_set_last_error(e);
      result = e.getResultNo();
   }
   return result;
}
