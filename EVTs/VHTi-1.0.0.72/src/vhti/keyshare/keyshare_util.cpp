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

#include "vhti/keyshare_util.h"
#include "vhti/genkeys.h"
#include <support/internal_error.h>
#include <support/bignum.h>
#include <support/random_internal.h>
#include <misc/xml_tree.h>
#include <misc/safe_xml_tree.h>
#include <util/sslerror.h>

#include <string>
#include <sstream>

#define USE_ENCRYPTION 1        // set to 0 to make ElGamal
                                // encryption trivial

int                           // seed, n, t, and DSA/Strong
VHTI_create_keygen_parameters(SeedParameters input_parameters,
                              RandomState random_state,
                              KeyGenParameters *output_parameters,
                              RandomState *random_state_out)
{
   // Assume success until told otherwise
   int result = 0;
   *output_parameters = NULL;
   *random_state_out = NULL;
   try 
   {
      // TODO -- consider seeding the OpenSSL PRNG with something
      // from our RandomState, so that this function always returns
      // the same outputs when called with the same inputs (for all I
      // know, the function already does that, but the OpenSSL docs
      // imply that BN_generate_prime uses the OpenSSL PRNG, and that
      // it seeds itself from various entropy sources in the system).
      
      // A RandomState object
      VHInternal::RS rs (random_state);
      // An xml tree from the input_parameters
      VHUtil::safe_xml_tree xml_in(input_parameters, SEED_PARAMETERS);

      // The Election Modulus
      auto_BN pm;
      // The Election Subgroup Modulus
      auto_BN qm;
      // The Election Subgroup Generator
      auto_BN gen;
      // An OpenSSL structure to hold BIGNUM temporary variables
      // used by library functions
      auto_BN_CTX ctx(BN_CTX_new());
      VH_nonzero (ctx, BN_CTX_NEW);

      // An empty xml tree to hold the KeyGenParameters
      VHUtil::xml_tree xml_kgp("<" KEY_GEN_PARAMETERS "/>");
      // A node to hold the CryptoGroupParameters
      VHUtil::xml_node node_cgp =
         xml_kgp.root ()->new_element(CRYPTO_GROUP_PARAMETERS);

      // Sanity-check: threshold must not exceed numauth.
      {
         BIGNUM *threshold = NULL; 
         BIGNUM *numauth   = NULL;
         VH_nonzero (BN_dec2bn (&threshold, xml_in.root ()->e(THRESHOLD)->characters ().c_str ()),
                     BADLY_FORMED_NUMBER);
         VH_nonzero (BN_dec2bn (&numauth,   xml_in.root ()->e(NUM_AUTH) ->characters ().c_str ()),
                     BADLY_FORMED_NUMBER);
         VH_zero (-1 == BN_cmp (numauth, threshold),
                  THRESHOLD_EXCEEDS_NUMAUTH);
         BN_free (numauth);
         BN_free (threshold);
      }

      // Generate primes p, q, and r, where q and r are relatively prime,
      // and p = qr + 1.
      
      VH_nonzero (BN_generate_prime(qm, 160, 0, NULL, NULL, NULL, NULL),
         BN_GENERATE_PRIME);
      // r = (p-1 / q),  make sure  r / q has a remainder
      auto_BN r_val;

      // The remainder
      auto_BN rem;

      while (BN_is_zero(rem))
      {
         VH_nonzero (BN_generate_prime(pm, 1024, 0, qm, NULL, NULL, NULL),
            BN_GENERATE_PRIME);
         auto_BN p_minus_one; // p - 1
         VH_nonzero (BN_sub(p_minus_one, pm, BN_value_one()), BN_SUB);

         VH_nonzero (BN_div(r_val, NULL, p_minus_one, qm, ctx), BN_DIV);
         VH_nonzero (BN_div(NULL, rem, r_val, qm, ctx), BN_DIV);
      }
      // A value in Zp*
      auto_BN tmp_gen;
      VHInternal::rand_range2 (BN_value_one(), pm, rs, tmp_gen);
      
#if !defined (USE_ENCRYPTION)
# error You must define USE_ENCRYPTION to be either 0 or 1
#endif

#if (0 == USE_ENCRYPTION)
#pragma message ("WARNING!!!! Using no encryption.")
         VHUtil::cout () << "WARNING!!!! Forcing so-called \"generator\" to one." << std::endl;
         VH_nonzero (BN_set_word (gen, 1), BN_SET_WORD);
#else
      // Our generator is this temporary number raised to (p-1)/q = r
      // Compute exponent
      VH_nonzero (BN_mod_exp(gen, tmp_gen, r_val, pm, ctx), BN_MOD_EXP);
#endif
      // Now add the new parameters to the new tree.
      add_BN_element(node_cgp, ELECTION_MODULUS, pm, DEC);
      add_BN_element(node_cgp, ELECTION_SUBGROUP_MODULUS, qm, DEC);
      add_BN_element(node_cgp, ELECTION_SUBGROUP_MEMBER, gen, DEC);
      // A node to hold na
      VHUtil::xml_node node_na = xml_kgp.root ()->new_element(NUM_AUTH);
      node_na->add_characters(xml_in.root ()->e(NUM_AUTH)->characters());
      // A node to hold th
      VHUtil::xml_node node_th = xml_kgp.root ()->new_element(THRESHOLD);
      node_th->add_characters(xml_in.root ()->e(THRESHOLD)->characters());
      // A stream to hold xml_kgp
      std::ostringstream out_stream;
      out_stream << xml_kgp;
      * output_parameters = VHTI_dup(out_stream.str().c_str());
      *random_state_out = VHTI_dup (rs);
   }
   catch (const VHUtil::Exception & e) 
   {
      VHTI_set_last_error(e);
      result = e.getResultNo();
   }
   return result;
}

int
VHTI_create_authority(const char *authority_id,
                      KeyGenParameters key_gen_parameters,
                      RandomState random_state,
                      const GeneralPurposePublicKey pu,
                      GeneralPurposePrivateKey *pr,
                      Authority *authority,
                      RandomState *random_state_out)
{
   // Assume success until told otherwise
   int result = 0;
   *authority = NULL;
   *random_state_out = NULL;
   
   try 
   {
      // Create a RandomStateobject
      VHInternal::RS rs (random_state);
      // An empty xml tree for the Authority object
      VHUtil::xml_tree xml_auth("<" AUTHORITY "/>");

      xml_auth.root ()->add_attribute(AUTH_FINGERPRINT, authority_id);
      
      // An xml tree from the key_gen_parameters input
      VHUtil::safe_xml_tree xml_params(key_gen_parameters, KEY_GEN_PARAMETERS);
      // The root node of xml_params
      VHUtil::xml_node root_kgp = xml_params.root();
      // The node with the CryptoGroupParameters
      VHUtil::xml_node node_cgp = root_kgp->e(CRYPTO_GROUP_PARAMETERS);
      // The value of the ElectionSubgroupModulus
      auto_BN qm = xml2BN(node_cgp->e(ELECTION_SUBGROUP_MODULUS));
      
      // Generate a random number in the subgroup q - this is the beta
      // value for the authority
      auto_BN beta(NULL);

      VHInternal::rand_range2(BN_value_one(), qm, rs, beta);
      // An xml tree to hold the Certificate
      VHUtil::xml_node node_cert = xml_auth.root ()->new_element(CERTIFICATE);
      {
         // Private Key
         auto_freeing<GeneralPurposePrivateKey> priv;
         // Public Key
         auto_freeing<GeneralPurposePublicKey>  pub;
         
         if (pu && *pu)
         {
            pub = VHTI_dup (pu);
            *pr = NULL;
         }
         else
         {
            // This is probably only useful for demos -- real
            // authorities probably want to generate keypairs on their
            // own, rather than trust the people running the election
            // to do it for them
            // An xml tree to hold identifying information
            VHUtil::xml_tree xml_ident ("<" IDENT_INFO "/>");
            xml_ident.root ()->add_characters (authority_id);
            
            {
               // A stream to hold xml_ident
               std::ostringstream tmp;
               tmp << *(xml_ident.root ());
               
               VH_propagate (VHTI_generate_keys(tmp.str ().c_str (),
                                                &priv,
                                                &pub),
                             GENERATE_KEYS);
            }
            *pr = VHTI_dup (priv);
         }

         // An xml tree containing the public key
         VHUtil::safe_xml_tree tmp ((const char *) pub, GENERAL_PURPOSE_PUBLIC_KEY);
         node_cert->add_element (tmp.root()->deep_copy ());
      }

      add_BN_element (xml_auth.root (), AUTHORITY_EVALUATION_POINT, beta);

      *authority = VHTI_dup(xml_auth.str().c_str());
      *random_state_out = VHTI_dup (rs);
   }
   catch (const VHUtil::Exception & e) 
   {
      VHTI_set_last_error(e);
      result = e.getResultNo();
   }
   return result;
}
