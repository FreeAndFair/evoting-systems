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

#include "vhti/gen_pubkey.h"
#include "vhti/keyshare_util.h"
#include <support/internal_error.h>
#include <support/bignum.h>
#include <support/xml_tree_group_check.h>
#include <keyshare/keyshare_internal.h>
#include <misc/xml_tree.h>

#include <string>
#include <sstream>
#include <vector>

// This function checks the broadcast values
// before generating the public key.

int
VHTI_generate_public_key (KeyGenParameters key_gen_parameters,
                          BroadcastValues broadcast_values,
                          ElectionPublicKey *public_key)
{
   // Assume success until told otherwise
   int result = 0;
   *public_key = NULL;
   // The Election Modulus
   auto_BN pm(NULL);
   // The Election Subgroup Modulus
   auto_BN qm(NULL);
   // The Election Subgroup Generator
   auto_BN gen(NULL);
   // The Election Public Key (for group check)
   auto_BN ePublicKey(NULL);
   // The number of authorities
   int na = 0;
   // The threshold number of authorities needed for tabulation
   int th = 0;
   // An OpenSSL structure that holds BIGNUM temporary variables
   // used by library functions
   auto_BN_CTX ctx(BN_CTX_new());
   // A vector to hold all of the Theta values of order 0
   std::vector< auto_BN > all_tht0;
   
   try
   {
      VH_nonzero (ctx, BN_CTX_NEW);
      result = (::VHTI_validate(KEY_GEN_PARAMETERS, key_gen_parameters)
         || ::VHTI_validate(BROADCAST_VALUES, broadcast_values));

      if (result != 0) throw VH_exception("VALIDATION_FAILURE");
      
      VHInternal::get_keygen_parameters (key_gen_parameters, pm, qm, gen,
         na, th);
      
      // First check the broadcast values:
      // An xml tree from the broadcast_values input
      VHUtil::xml_tree_group_check xml_bvs(broadcast_values, pm, qm, gen, ePublicKey);

      for (int i=0; i<xml_bvs.root ()->element_count(); i++)
      {
         // The "s" value
         auto_BN something = xml2BN(xml_bvs.root ()->e(i)->e(SOMETHING));
         // The omega value
         auto_BN omega = xml2BN(xml_bvs.root ()->e(i)->e(OMEGA));
         // The Theta of order 0
         auto_BN tht0 = xml2BN(xml_bvs.root ()->e(i)->e(BIG_THETA, ORDER, "0"));
         
         // Get a Hash of theta0 and omega
         auto_BN hashval;
         // The hash value before taking the modulus
         auto_BN tmp_hash = GetHashOf2BNs(tht0, omega);
         VH_nonzero (BN_mod(hashval, tmp_hash, qm, ctx), BN_MOD);
         
         // Save ThetaOrder0 elements in a vector to make the public key
         all_tht0.push_back(tht0);
         
         // For each authority, check that the values satisfy the equation
         // ElectionSubgroupGenerator^Something = Omega*(ThetaOrder0^Hash).
         auto_BN lhs;
         auto_BN rhs;
         auto_BN tmp;
         VH_nonzero (BN_mod_exp(lhs, gen, something, pm, ctx), BN_MOD_EXP);
         VH_nonzero (BN_mod_exp(tmp, tht0, hashval, pm, ctx), BN_MOD_EXP);
         VH_nonzero (BN_mod_mul(rhs, omega, tmp, pm, ctx), BN_MOD_MUL);
         
         VH_zero (BN_cmp(lhs, rhs), COMMITTMENT_ZKP_PROOF_DIDNT_CHECK);
      }
      
      // Must have BroadcastValues from ALL authorities to
      // generate the public key.
      VH_nonzero (all_tht0.size() == na, WRONG_NUMBER_OF_BIG_THETAS);

      // An empty xml tree for the ElectionPublicKey
      VHUtil::xml_tree xml_pk("<" ELECTION_PUBLIC_KEY "/>");
      // Multipy all ThetaOrder0 elements together
      // The PublicKey value
      auto_BN pk_value (BN_value_one());

      for (i=0; i<all_tht0.size(); i++)
      {
         VH_nonzero (BN_mod_mul(pk_value, pk_value, all_tht0[i], pm, ctx),
                     BN_MOD_MUL);
      }
      // Insert it into the ElectionPublicKey xml.
      add_BN_characters(xml_pk.root (), pk_value, DEC);

      *public_key = VHTI_dup(xml_pk.str().c_str());
   }
   catch (const VHUtil::Exception & e)
   {
      VHTI_set_last_error(e);
      result = e.getResultNo();
   }
   
   return result;
}
