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

#include "vhti/gen_comm.h"
#include "vhti/keyshare_util.h"
#include <support/internal_error.h>
#include <support/support_internal.h>
#include <support/bignum.h>
#include <support/xml_tree_group_check.h>
#include <keyshare/keyshare_internal.h>
#include <misc/xml_tree.h>

#include <string>
#include <sstream>

// This operation will use the broadcast values
// to check the pairwise secrets received by one authority.

int
VHTI_generate_commitment (KeyGenParameters key_gen_parameters,
                          // This is the recipient of the following secrets
                          Authority authority,
                          BroadcastValues all_broadcast_values,
                           // Where the ToID is the above authority
                          PairwiseSecrets pairwise_secrets,
                          SecretShare *secret_share,
                          KeyShareCommitment *keyshare_commitment)
                          
{
  
   int result = 0; // Assume success until told otherwise
   *secret_share = NULL;
   *keyshare_commitment = NULL;
   auto_BN pm(NULL); // The Election Modulus
   auto_BN qm(NULL); // The Election Subgroup Modulus
   auto_BN gen(NULL); // The Election Subgroup Generator
   auto_BN ePublicKey(NULL); // The Election Public Key
   int na = 0; // The number of authorities
   int th = 0; // The threshold number of authorities needed for tabulation
   // An OpenSSL structure that holds BIGNUM temporary variables
   // used by library functions
   auto_BN_CTX ctx(BN_CTX_new());
   // A map of the id of the originator and the secret value
   std::map< std::string, auto_BN > secret_values;
   std::map< std::string, auto_BN >::iterator m_it; // An iterator for the map
   std::string to_id; // The id of the receiver of the secret
   
   try
   {
      VH_nonzero (ctx, BN_CTX_NEW);
      result = (::VHTI_validate(KEY_GEN_PARAMETERS, key_gen_parameters)
         || ::VHTI_validate(AUTHORITY, authority)
         || ::VHTI_validate(BROADCAST_VALUES, all_broadcast_values)
         || ::VHTI_validate(PAIRWISE_SECRETS, pairwise_secrets));

      if (result != 0) throw VH_exception("VALIDATION_FAILURE");

      VHInternal::get_keygen_parameters (key_gen_parameters, pm, qm, gen,
         na, th);
      
      // Check pairwise secrets before continuing.
      // You must have broadcast values from ALL authorities.
      
      // Get Beta for AuthCertFingerprint=ToID from authority_id object.
      VHUtil::xml_tree_group_check xml_auth(authority, pm, qm, gen, ePublicKey);
      VHUtil::xml_node root_auth = xml_auth.root(); // The root node of xml_auth
      to_id = root_auth->attribute(AUTH_FINGERPRINT);
      // The node of the AuthorityEvaluationPoint
      VHUtil::xml_node node_beta = root_auth->e(AUTHORITY_EVALUATION_POINT);
      auto_BN beta = xml2BN(node_beta); // The value of beta
      
      // Put secrets for authority_id into a map with who is the sender.
      // An xml tree from the pairwise_secrets input
      VHUtil::xml_tree_group_check xml_pws(pairwise_secrets, pm, qm, gen, ePublicKey);

      for (int j=0; j<xml_pws.root ()->element_count() ; j++)
      {
         // The id of the originator of the secret
         const std::string from_id = xml_pws.root ()->e(j)->attribute(FROM_ID);

         VH_nonzero (secret_values.find(from_id) == secret_values.end (), DUPLICATE_SECRET);

         secret_values.insert(std::pair< std::string, auto_BN >
                              (from_id, xml2BN(xml_pws.root ()->e(j))));
      }

      VH_nonzero (secret_values.size () == na, NUMBER_OF_SECRETS_NOT_EQUAL_TO_NUMBER_OF_AUTHORITIES);
      
      // An xml tree from the all_broadcast_values input
      VHUtil::xml_tree_group_check xml_bvs(all_broadcast_values, pm, qm, gen, ePublicKey);
      VHInternal::sanity_check_auth_fingerprints (na,
                                                  xml_bvs);
      // For each broadcast:
      // Get Thetas from broadcast_values for AuthFingerprint = FromID
      // Pay attention to attribute Order.

      for (int i=0; i<xml_bvs.root ()->element_count(); i++)
      {
         // A vector to hold the Theta values for each authority
         std::vector< auto_BN > tht_beta;
         // The current set of broadcast values
         VHUtil::xml_node node_bv = xml_bvs.root ()->e(i);

         for (int k=0; k<node_bv->element_count(); k++)
         {
            // The current broadcast value element
            VHUtil::xml_node current_node = node_bv->e(k);
            if (current_node->name() == BIG_THETA)
            {
              
               auto_BN tht = xml2BN(current_node); // The value of Theta
               // The order of Theta
               int tmp_order =
                  VHInternal::int_from_attribute(current_node, ORDER);
               // An auto_BN to hold the order attribute
               auto_BN orderBN;
               VH_nonzero (BN_set_word(orderBN, tmp_order), BN_SET_WORD);
               
               auto_BN tmp_exp1; // raise beta to the Order
               VH_nonzero (BN_mod_exp(tmp_exp1, beta, orderBN, qm, ctx),
                  BN_MOD_EXP);
               
               auto_BN tmp_exp2; // then raise the coefficient to this exponent
               VH_nonzero (BN_mod_exp(tmp_exp2, tht, tmp_exp1, pm, ctx),
                  BN_MOD_EXP);
               
               tht_beta.push_back(tmp_exp2); // put quotients in a vector
            }
         }

         VH_nonzero (tht_beta.size() == th, WRONG_NUMBER_OF_BIG_THETAS);
         
         // multiply( Theta0, Theta1^Beta,
         // ... , ThetaThreshold^(Beta^Threshold-1) ) 
         auto_BN secret_chk_val;
         BN_one(secret_chk_val);
         for (int iv=0; iv<tht_beta.size(); iv++)
         {
            VH_nonzero (BN_mod_mul(secret_chk_val, secret_chk_val,
                                   tht_beta[iv], pm, ctx), BN_MOD_MUL);
         }
         
         // Check that g^(PairwiseSecret Value from authority=from_id)
         // equals the above product
         m_it = secret_values.find(node_bv->attribute(AUTH_FINGERPRINT));
         VH_nonzero (m_it != secret_values.end (), NO_SECRET_FROM_AUTHORITY);
         auto_BN secret = m_it->second; // Secret associated with this from_id
         auto_BN g_exp; // g^secret

         VH_nonzero (BN_mod_exp(g_exp, gen, secret, pm, ctx), BN_MOD_EXP);
         VH_zero (BN_cmp(secret_chk_val, g_exp), PAIRWISE_SECRET_DIDNT_CHECK);
      }

      // An empty xml tree to hold the SecretShare
      VHUtil::xml_tree xml_ss("<" SECRET_SHARE "/>");
      VHUtil::xml_node root_ss = xml_ss.root(); // The root node of xml_ss
      // An empty xml tree to hold the KeyShareCommitment
      VHUtil::xml_tree xml_ksc("<" KEY_SHARE_COMMITMENT "/>");
      VHUtil::xml_node root_ksc = xml_ksc.root(); // The root node of xml_ksc
         
      // All pairwise secret values added together is my secret share.
      auto_BN ss;
      BN_zero(ss);
      for (m_it  = secret_values.begin ();
           m_it != secret_values.end ();
           m_it++)
      {
         VH_nonzero (BN_add(ss, ss, m_it->second), BN_ADD);
         ss.Canonicalize(qm);
      }
      add_BN_characters(root_ss, ss, DEC);
         
      // Raise ElectionSubgroupGenerator to my secret share.
      auto_BN ksc; // This is my key share commitment.
      VH_nonzero (BN_mod_exp(ksc, gen, ss, pm, ctx), BN_MOD_EXP);
      add_BN_characters(root_ksc, ksc, DEC);
      root_ksc->add_attribute(AUTH_FINGERPRINT, to_id.c_str());
      std::ostringstream ss_stream; // A stream to hold the SecretShare
      ss_stream << xml_ss;
      *secret_share = VHTI_dup(ss_stream.str().c_str());
      std::ostringstream ksc_stream; // Stream to hold the KeyShareCommitment
      ksc_stream << xml_ksc;
      *keyshare_commitment = VHTI_dup(ksc_stream.str().c_str());
   }
   catch (const VHUtil::Exception & e)
   {
      VHTI_set_last_error(e);
      result = e.getResultNo();
   }
   
   return result;
}
