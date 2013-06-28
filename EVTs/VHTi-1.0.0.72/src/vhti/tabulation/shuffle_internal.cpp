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

#pragma warning(disable: 4786)
#include <tabulation/shuffle_internal.h>
#include <tabulation/tabulation_internal.h>
#include "tabulation/private_elements.h"
#include <support/support_internal.h>
#include <support/internal_error.h>
#include "vhti/random.h"
#include "vhti/permutation.h"
#include "vhti/check_partial_decrypt.h"
#include <support/random_internal.h>
#include <misc/xml_tree.h>
#include <misc/safe_xml_tree.h>
#include <misc/vh_excpt.h>

#include <string>
#include <sstream>
#include <set>

int
VHInternal::shuffle_el_gamal_sequence
(const char * X_values,
 const char * Y_values,
 SignedBlankBallot signed_blank_ballot,
 GeneralPurposePublicKey ballot_signing_key,
 RandomState random_state,
 const char **X_values_out,
 const char **Y_values_out,
 RandomState *random_state_out,
 ShuffleValidityProof *shuffle_validity_proof)
 
{
   int result = 0; // Assume success until told otherwise
   int icount = 0; // A counter used for loops
   *X_values_out = NULL;
   *Y_values_out = NULL;
   *random_state_out = NULL;
   *shuffle_validity_proof = NULL;
   // An OpenSSL structure that holds BIGNUM temporary variables
   // used by library functions
   auto_BN_CTX ctx(BN_CTX_new());
   auto_BN pm(NULL); // The Election Modulus
   auto_BN qm(NULL); // The Election Subgroup Modulus
   auto_BN gen(NULL); // The Election Subgroup Generator
   auto_BN ePublicKey(NULL); // The Election Public Key
   VHUtil::safe_xml_tree xml_bb (signed_blank_ballot, BLANK_BALLOT, ballot_signing_key);

   try {
      result = (::VHTI_validate(RANDOM_STATE, random_state)) ;

      if (result != 0) throw VH_exception("VALIDATION_FAILURE");
      VHInternal::get_election_parameters(xml_bb, pm,
                                          qm, gen, ePublicKey);

      // An empty xml tree to hold the ShuffleValidityProof
      VHUtil::xml_tree xml_svp("<" SHUFFLE_VALIDITY_PROOF "/>");
      VHUtil::xml_node root_svp = xml_svp.root(); // The root node of xml_svp
      
      // An xml tree from the X_values input
      VHUtil::xml_tree xml_Xvalues(X_values);
      // The root node of xml_Xvalues
      VHUtil::xml_node root_Xvalues = xml_Xvalues.root();
      int ksize = root_Xvalues->element_count(); // The number of ballots
      
      auto_freeing< ConstCharStar > X_values_shuf = 0; // The shuffled X values
      auto_freeing< ConstCharStar > Y_values_shuf = 0; // The shuffled Y values
      // The return random state from various functions
      auto_freeing< RandomState > return_random_state = 0;
      
      bool shuffle_collision = true;
      while (shuffle_collision == true)
      {
         // Generate a random permutation of size k
         auto_freeing< Permutation > permutation = 0;
         VH_propagate(VHTI_get_permutation(random_state, ksize,
            &permutation, &return_random_state), GEN_SECRET_SHUFFLE_VALUES);
         random_state = VHTI_dup(return_random_state);
         
         // Random values associated with ballots and questions
         auto_freeing< ConstCharStar > beta_ji_values = 0;
         
         VH_propagate(generate_raw_ballot_output(xml_bb,
            X_values, Y_values, permutation, random_state, &X_values_shuf, &Y_values_shuf,
            &beta_ji_values, &return_random_state),
            GEN_RAW_BALLOT_OUTPUT);
         random_state = VHTI_dup(return_random_state);
         
         // The products of each ballot's X values
         auto_freeing< ConstCharStar > X_hats = 0;
         // The products of each ballot's Y values
         auto_freeing< ConstCharStar > Y_hats = 0;
         // The products of each ballot's Xbar values
         auto_freeing< ConstCharStar > X_checks = 0;
         // The products of each ballot's Ybar values
         auto_freeing< ConstCharStar > Y_checks = 0;
         // Random values associated with each question
         auto_freeing< ConstCharStar > e_values = 0;
         
         generate_el_gamal_sequences(xml_bb,
                                     X_values, Y_values,
                                     X_values_shuf, Y_values_shuf,
                                     &X_hats, &Y_hats,
                                     &X_checks, &Y_checks,
                                     &e_values);
         
         // Secrets used to generate proof elements
         auto_freeing< ConstCharStar > secret_shuffle_values = 0;
         VH_propagate(generate_secret_shuffle_values(xml_bb,
            permutation, beta_ji_values, e_values, ksize,
            random_state, &secret_shuffle_values, &return_random_state),
            GEN_SECRET_SHUFFLE_VALUES);
         
         // A string from secret_shuffle_values
         std::string str_secrets(secret_shuffle_values);
         // An xml tree from str_secrets
         VHUtil::xml_tree xml_secrets(str_secrets);
         // The root node of xml_secrets
         VHUtil::xml_node root_secrets = xml_secrets.root();

         // Proof values
         auto_freeing< ConstCharStar > public_shuffle_values = 0;
         VH_propagate(generate_public_shuffle_values(xml_bb, X_hats, Y_hats, secret_shuffle_values,
            &public_shuffle_values), SHUFFLE_GEN_PUBLIC_VALUES);
         
         // A string from public_shuffle_values
         std::string str_public(public_shuffle_values);
         // An xml tree from str_public
         VHUtil::xml_tree xml_public(str_public);
         // The root node of xml_public
         VHUtil::xml_node root_public = xml_public.root();
         
         // The returning hash values
         auto_freeing< ConstCharStar > rho_values = 0;
         VH_propagate(generate_shuffle_hash_values
                      (xml_bb,
                       X_hats, Y_hats, public_shuffle_values,
                       X_checks, Y_checks, &rho_values), SHUFFLE_GEN_HASH_VALUES);
         
         // The final values we will need for our proof
         auto_freeing< ConstCharStar > final_shuffle_values = 0;
         bool fv_collision = false;
         VH_propagate (generate_final_shuffle_values (xml_bb,
            secret_shuffle_values,
            rho_values,
            &final_shuffle_values,
            fv_collision),
            FINAL_SHUFFLE_VALUES);

         shuffle_collision = fv_collision;
         
         // Generate a new random state in case we loop here
         std::string srs2(random_state); // A string from random_state
         // An empty xml_tree to hold the RandomSeedKey
         VHUtil::xml_tree xml_rskey2("<" RANDOM_SEED_KEY "/>");
         xml_rskey2.root()->add_characters(srs2);

         auto_freeing< RandomState > new_rs2 = 0; // The new RandomState
         VH_propagate(VHTI_generate_random_state(xml_rskey2.str().c_str(),
            &new_rs2), SHUFFLE_GENERATE_RANDOM_STATE);
         random_state = VHTI_dup(new_rs2);
         
         if (fv_collision)
         {
            continue;
         }

         // A string from the final_shuffle_values
         std::string str_final(final_shuffle_values);
         // An xml tree from str_final
         VHUtil::xml_tree xml_final(str_final);
         // The root node of xml_final
         VHUtil::xml_node root_final = xml_final.root();
         // The node containing the sigma_values
         VHUtil::xml_node node_sigma_values =
            root_final->e(SIGMA_VALUES);
         // The node containing the tau values
         VHUtil::xml_node node_tau = root_final->e(TAU);

         // Call simple shuffle here
         // The simple proof that is returned from simple_k_shuffle
         auto_freeing<SimpleShuffleValidityProof>
            simple_shuffle_validity_proof = 0;
         bool simple_collision = false;
         VH_propagate(simple_k_shuffle(xml_bb,
                                       root_final->e(R_VALUES)->str().c_str(),
                                       root_secrets->e(GAMMA)->str().c_str(),
                                       root_secrets->e(PERMUTATION)->str().c_str(),
                                       root_secrets->e(NUU)->str().c_str(),
                                       random_state, &simple_shuffle_validity_proof,
                                       &return_random_state, simple_collision), SIMPLE_K_SHUFFLE);
         shuffle_collision = simple_collision;
            
         // Generate a new random state in case we loop here
         std::string srs3(random_state); // A string from random_state
         // An empty xml tree to hold the RandomSeedKey
         VHUtil::xml_tree xml_rskey3("<" RANDOM_SEED_KEY "/>");
         xml_rskey3.root()->add_characters(srs3);

         auto_freeing< RandomState > new_rs3 = 0; // The new RandomState
         VH_propagate(VHTI_generate_random_state(xml_rskey3.str().c_str(),
                                                 &new_rs3), SHUFFLE_GENERATE_RANDOM_STATE);
         random_state = VHTI_dup(new_rs3);
            
         // Don't put things into SVP until sure we have a Simple Proof
         if (simple_collision)
         {
            continue;
         }

         for (icount=0; icount<root_public->element_count(); icount++)
         {  // Need BigGamma to calculate hash, so convenient to have
            // it in public values, but SVP comes from simple shuffle.
            if ( (root_public->e(icount)->name() != BIG_GAMMA) &&
                 (root_public->e(icount)->name() != G_VALUE) )
            {
               root_svp->add_element
                  (root_public->e(icount)->deep_copy());
            }
         }
               
         // Add sigma and tau into ShuffleValidityProof
         root_svp->add_element(node_sigma_values->deep_copy());
         root_svp->add_element(node_tau->deep_copy());
               
         // Add simple shuffle proof objects to shuffle proof objects
         // to make the complete proof
         // A string from the simple_shuffle_validity_proof
         std::string ssvp_str(simple_shuffle_validity_proof);
         // An xml tree from ssvp_str
         VHUtil::xml_tree xml_ssvp(ssvp_str);
         // The root node of xml_ssvp
         VHUtil::xml_node root_ssvp = xml_ssvp.root();
         root_svp->add_element(root_ssvp->deep_copy());
      }

      *X_values_out = VHTI_dup(X_values_shuf);
      *Y_values_out = VHTI_dup(Y_values_shuf);
      *shuffle_validity_proof = VHTI_dup(xml_svp.str().c_str());
      *random_state_out = VHTI_dup(return_random_state);
   }
   catch (const VHUtil::Exception & e) {
      VHTI_set_last_error(e);
      result = e.getResultNo();
   }
   return result;
}

int
VHInternal::generate_secret_shuffle_values
(VHUtil::xml_tree &xml_bb,
 Permutation permutation,
 const char * beta_ji_values,
 const char * e_values,
 int ksize,
 RandomState random_state,
 const char **secret_shuffle_values,
 RandomState *random_state_out)
{
   int result = 0; // Assume success until told otherwise
   *random_state_out = NULL;
   *secret_shuffle_values = NULL;
   int icount = 0; // A counter used for loops
   // An OpenSSL structure that holds BIGNUM temporary variables
   // used by library functions
   auto_BN_CTX ctx(BN_CTX_new());
   auto_BN pm(NULL); // The Election Modulus
   auto_BN qm(NULL); // The Election Subgroup Modulus
   auto_BN gen(NULL); // The Election Subgroup Generator
   auto_BN ePublicKey(NULL); // The Election Public Key
   
   try {
      VHInternal::RS rs (random_state); // A random state object
      // An empty xml tree to hold the ShuffleSecretValues
      VHUtil::xml_tree xml_secrets("<ShuffleSecretValues/>");

      VHInternal::get_election_parameters(xml_bb,
         pm, qm, gen, ePublicKey);

      // An xml tree from the permutation input
      VHUtil::xml_tree xml_perm(permutation);
      // The root node of xml_perm
      VHUtil::xml_node root_perm = xml_perm.root();
      xml_secrets.root ()->add_element(root_perm->deep_copy());
      // A vector of the permutation values
      std::vector<int> perm_vec = get_permutation_vector_from_xml(permutation);

      // An xml tree from the beta_ji_values input
      VHUtil::xml_tree xml_ji_betas(beta_ji_values);
      // The root node of xml_ji_betas
      VHUtil::xml_node root_ji_betas = xml_ji_betas.root();

      // An xml tree from the e_values input
      VHUtil::xml_tree xml_e_values(e_values);
      // The root node of xml_e_values
      VHUtil::xml_node root_e_values = xml_e_values.root();
      // The number of questions per ballot
      int num_questions = root_e_values->element_count();
      
      // Generate beta values in Zq* = SUM(e_j * beta_ji)
      // A node for beta values
      VHUtil::xml_node root_betas = xml_secrets.root ()->new_element(BETA_VALUES);
      // A vector to hold the beta values
      std::vector< auto_BN > beta_vec; // useful for calculating tau_1

      for (icount=0; icount<ksize; icount++)
      {
         auto_BN beta_value; // The value we are calculating
         VH_nonzero(BN_zero(beta_value), BN_ZERO);
         // The current beta ji ballot
         VHUtil::xml_node cur_beta_ji_bal = root_ji_betas->e(BALLOT, icount);
         for (int j=0; j<num_questions; j++)
         {
            // The current e value
            VHUtil::xml_node current_e_value = root_e_values->e(j);
            // The current beta ji value
            VHUtil::xml_node current_beta_ji_val = cur_beta_ji_bal->e(j);
            auto_BN prod; // The product of e and beta_ji
            VH_nonzero(BN_mod_mul(prod, xml2BN(current_e_value),
                                  xml2BN(current_beta_ji_val), qm, ctx), BN_MOD_MUL);
            VH_nonzero(BN_add(beta_value, beta_value, prod), BN_ADD);
            beta_value.Canonicalize(qm);
         }
         add_BN_element(root_betas, "beta", beta_value, DEC);
         beta_vec.push_back(beta_value);
      }

      // A node for u values
      VHUtil::xml_node root_u = xml_secrets.root ()->new_element(U_VALUES);
      // A node for w values
      VHUtil::xml_node root_w = xml_secrets.root ()->new_element(W_VALUES);
      // A node for a values
      VHUtil::xml_node root_a = xml_secrets.root ()->new_element(A_VALUES);
      std::vector< auto_BN > w_vec; // A vector to hold the w values
      
      // Generate random sequence a in Zq*
      // Generate random sequences u and w in Zq
      // A set to hold a values so we can ensure that they are unique
      std::set< auto_BN > a_set;
      for (icount=0; icount<ksize; icount++)
      {
         auto_BN one_bn; // An auto_BN with the value of 1
         VH_nonzero(BN_one(one_bn), BN_ONE);
         auto_BN u_value; // The u value we will calculate
         auto_BN w_value; // The w value we will calculate
         auto_BN a_value; // The a value we will calculate

         VHInternal::rand_range(qm, rs, u_value);
         add_BN_element(root_u, U_VALUE, u_value, DEC);

         VHInternal::rand_range(qm, rs, w_value);
         add_BN_element(root_w, W_VALUE, w_value, DEC);
         w_vec.push_back(w_value);

         do  // Ensures that you end up with a set of a values that are unique
            VHInternal::rand_range2(one_bn, qm, rs, a_value);
         while ( a_set.end() != a_set.find(a_value) );

         add_BN_element(root_a, A_VALUE, a_value, DEC);
         a_set.insert(a_value);
      }
      
      auto_BN gamma;  // Generate random gamma in Zq*
      auto_BN one_bn; // An auto_BN with the value of 1
      VH_nonzero(BN_one(one_bn), BN_ONE);
      VHInternal::rand_range2(one_bn, qm, rs, gamma);
      add_BN_element(xml_secrets.root (), "gamma", gamma, DEC);

      auto_BN nuu;  // Generate random nu in Zq*
      VHInternal::rand_range2(one_bn, qm, rs, nuu);
      add_BN_element(xml_secrets.root (), "nuu", nuu, DEC);
      
      auto_BN tau_0;  // Generate tau_0 in Zq
      VHInternal::rand_range(qm, rs, tau_0);
      add_BN_element(xml_secrets.root (), "tau_0", tau_0, DEC);
      
      auto_BN sum_value;  // The sum of the w*beta values
      VH_nonzero(BN_zero(sum_value), BN_ZERO);
      auto_BN tau_1;  // Compute tau_1 = tau_0 + SUM[1-k] ( w * beta_pi(i) )
      for (icount=0; icount<ksize; icount++) {
         // The product of w and beta_pi_i
         auto_BN prod_value;
         // The value of the permutation at icount
         int pval = perm_vec[icount];
         // The value of beta at the permutation index
         auto_BN betap_value = beta_vec[pval-1];
         VH_nonzero (BN_mod_mul(prod_value, w_vec[icount], betap_value,
            qm, ctx), "GSSVMUL");
         VH_nonzero (BN_add(sum_value, sum_value, prod_value),
            "GSSVADD1");
         sum_value.Canonicalize(qm);
      }
      VH_nonzero (BN_add(tau_1, sum_value, tau_0), "GSSVADD2");
      tau_1.Canonicalize(qm);
      add_BN_element(xml_secrets.root (), "tau_1", tau_1, DEC);
      std::ostringstream oss_secrets; // A stream to hold xml_secrets
      oss_secrets << xml_secrets;
      *secret_shuffle_values = VHTI_dup(oss_secrets.str().c_str());
      *random_state_out = VHTI_dup (rs);
   }
   catch (const VHUtil::Exception & e) {
      VHTI_set_last_error(e);
      result = e.getResultNo();
   }
   return result;
}

int
VHInternal::generate_raw_ballot_output(VHUtil::xml_tree &xml_bb,
                                       const char * X_values,
                                       const char * Y_values,
                                       Permutation permutation,
                                       RandomState random_state,
                                       const char **X_values_out,
                                       const char **Y_values_out,
                                       const char **beta_ji_values,
                                       RandomState *random_state_out)
{
   int result = 0; // Assume success until told otherwise
   *X_values_out = NULL;
   *Y_values_out = NULL;
   *beta_ji_values = NULL;
   *random_state_out = NULL;
   int icount = 0; // A counter used for loops
   auto_BN pm(NULL); // The Election Modulus
   auto_BN qm(NULL); // The Election Subgroup Modulus
   auto_BN gen(NULL); // The Election Subgroup Generator
   auto_BN ePublicKey(NULL); // The Election Public Key
   // An OpenSSL structure that holds BIGNUM temporary variables
   // used by library functions
   auto_BN_CTX ctx(BN_CTX_new());
   
   try {
      VHInternal::RS rs (random_state); // A RandomState object
      VHInternal::get_election_parameters(xml_bb, pm,
         qm, gen, ePublicKey);
      VHUtil::xml_node root_bb = xml_bb.root();

      VHUtil::xml_tree xml_Xvalues(X_values); // An xml tree from X_values input
      // The root node of xml_Xvalues
      VHUtil::xml_node root_Xvalues = xml_Xvalues.root();
      VHUtil::xml_tree xml_Yvalues(Y_values); // An xml tree from Y_values input
      // The root node of xml_Yvalues
      VHUtil::xml_node root_Yvalues = xml_Yvalues.root();
      int ksize = root_Xvalues->element_count(); // The number of ballots
      int num_questions = 0; // How many questions in a ballot
      int num_elems_bb = root_bb->element_count();
      for (int i=0; i<num_elems_bb; i++)
      {
         if (root_bb->e(i)->name() == BALLOT_QUESTION)
         {
            num_questions++;
         }
      }
      // A vector to hold the values of the permutation
      std::vector<int> perm_vec = get_permutation_vector_from_xml(permutation);

      // Generate a unique beta for each question for each ballot
      // An empty xml tree to hold the beta_ji_values
      VHUtil::xml_tree xml_ji_betas("<beta_ji_values/>");
      // The root node of xml_ji_betas
      VHUtil::xml_node root_ji_betas = xml_ji_betas.root();
      for (icount=0; icount<ksize; icount++) {
         VHUtil::xml_node root_beta_bal = root_ji_betas->new_element(BALLOT);
         for (int qsize=0; qsize<num_questions; qsize++) {
            auto_BN one_bn; // An auto_BN with the value of 1
            VH_nonzero(BN_one(one_bn), BN_ONE);
            auto_BN beta_value; // The random beta value
            VHInternal::rand_range2(one_bn, qm, rs, beta_value);
            add_BN_element(root_beta_bal, "beta", beta_value, DEC);
         }
      }
      std::ostringstream oss_ji_betas; // A stream to hold xml_ji_betas
      oss_ji_betas << xml_ji_betas;

      // Xbar = g^(beta_j_pi(i)) * X_j_pi(i)
      // Ybar = h^(beta_j_pi(i)) * Y_j_pi(i)
      // An empty xml tree to hold the Xbar values
      VHUtil::xml_tree xml_Xbar("<Xbar_values/>");
      VHUtil::xml_node root_Xbar = xml_Xbar.root(); // The root node of xml_Xbar
      for (icount=0; icount<root_Xvalues->element_count(); icount++)
      { // Copy X and Y values into Xbar and Ybar for placeholders
         root_Xbar->add_element(root_Xvalues->e(icount)->deep_copy());
      }
      VHUtil::xml_tree xml_Ybar("<Ybar_values/>");  // xml tree for Ybar values
      VHUtil::xml_node root_Ybar = xml_Ybar.root(); // The root node of xml_Ybar
      for (icount=0; icount<root_Yvalues->element_count(); icount++) {
         root_Ybar->add_element(root_Yvalues->e(icount)->deep_copy());
      }
      for (icount=0; icount<ksize; icount++)
      {  // The value of the permutation at index icount
         int pval = perm_vec[icount];
         // The X values of the current ballot
         VHUtil::xml_node current_X_ballot = root_Xvalues->e(BALLOT, pval-1);
         // The Y values of the current ballot
         VHUtil::xml_node current_Y_ballot = root_Yvalues->e(BALLOT, pval-1);
         // The Xbar values of the current ballot
         VHUtil::xml_node current_Xbar_ballot = root_Xbar->e(BALLOT, icount);
         // The Ybar values of the current ballot
         VHUtil::xml_node current_Ybar_ballot = root_Ybar->e(BALLOT, icount);
         // The beta values of the current ballot
         VHUtil::xml_node current_beta_ji_ballot =
            root_ji_betas->e(BALLOT, pval-1);

         for (int j=0; j<num_questions; j++)
         {  // The value of beta_ji for the current question and ballot
            auto_BN betap_value = xml2BN(current_beta_ji_ballot->e(j));
            auto_BN Xbar_value; // The Xbar value we will calculate
            auto_BN Ybar_value; // The Ybar value we will calculate
            auto_BN g_exp; // The value of g^beta_pi_i
            auto_BN h_exp; // The value of h^beta_pi_i
            VHInternal::fixed_mod_exp(g_exp, gen, betap_value, pm,
                                      ctx);
            VHInternal::fixed_mod_exp(h_exp, ePublicKey,
                                      betap_value, pm, ctx);
            VH_nonzero(BN_mod_mul(Xbar_value, g_exp, xml2BN(current_X_ballot->e(j)),
                                  pm,ctx), BN_MOD_MUL);
            VH_nonzero(BN_mod_mul(Ybar_value, h_exp, xml2BN(current_Y_ballot->e(j)),
                                  pm,ctx), BN_MOD_MUL);
            current_Xbar_ballot->e(X_VALUE, j)->erase_all_characters();
            add_BN_characters(current_Xbar_ballot->e(X_VALUE, j),
                              Xbar_value, DEC);
            current_Ybar_ballot->e(Y_VALUE, j)->erase_all_characters();
            add_BN_characters(current_Ybar_ballot->e(Y_VALUE, j),
                              Ybar_value, DEC);
         }
      }
      std::ostringstream oss_Xbar; // A stream to hold xml_Xbar
      oss_Xbar << xml_Xbar;
      std::ostringstream oss_Ybar; // A stream to hold xml_Ybar
      oss_Ybar << xml_Ybar;
      *X_values_out = VHTI_dup(oss_Xbar.str().c_str());
      *Y_values_out = VHTI_dup(oss_Ybar.str().c_str());
      *beta_ji_values = VHTI_dup(oss_ji_betas.str().c_str());
      *random_state_out = VHTI_dup (rs);
   }
   catch (const VHUtil::Exception & e) {
      VHTI_set_last_error(e);
      result = e.getResultNo();
   }
   return result;
}

int
VHInternal::generate_public_shuffle_values
(VHUtil::xml_tree &xml_bb,
 const char * X_values,
 const char * Y_values,
 const char *secret_shuffle_values,
 const char **public_shuffle_values)
{
   int result = 0; // Assume success until told otherwise
   *public_shuffle_values = NULL;
   int icount = 0; // A counter used for loops
   auto_BN pm(NULL); // The Election Modulus
   auto_BN qm(NULL); // The Election Subgroup Modulus
   auto_BN gen(NULL); // The Election Subgroup Generator
   auto_BN ePublicKey(NULL); // The Election Public Key
   // An OpenSSL structure that holds BIGNUM temporary variables
   // used by library functions
   auto_BN_CTX ctx(BN_CTX_new());
   
   try
   {
      // An empty xml tree to hold ShufflePublicValues
      VHUtil::xml_tree xml_public("<ShufflePublicValues/>");
      // The root node of xml_public
      VHUtil::xml_node root_public = xml_public.root();
      
      VHInternal::get_election_parameters(xml_bb, pm, qm,
         gen, ePublicKey);
      
      // An xml tree from the X_values input
      VHUtil::xml_tree xml_Xvalues(X_values);
      // The root node of xml_Xvalues
      VHUtil::xml_node root_Xvalues = xml_Xvalues.root();
      // An xml tree from the Y_values input
      VHUtil::xml_tree xml_Yvalues(Y_values);
      // The root node of xml_Yvalues
      VHUtil::xml_node root_Yvalues = xml_Yvalues.root();
      int ksize = root_Xvalues->element_count(); // The number of ballots
      
      // Get the secret shuffle values out of xml
      // An xml tree from the secret_shuffle_values input
      VHUtil::xml_tree xml_secrets(secret_shuffle_values);
      // The root node of xml_secrets
      VHUtil::xml_node root_secrets = xml_secrets.root();
      // The node containing the permutation
      VHUtil::xml_node root_perm = root_secrets->e(PERMUTATION);
      // The node containing the beta_values
      VHUtil::xml_node root_beta = root_secrets->e(BETA_VALUES);
      // The node containing the u_values
      VHUtil::xml_node root_u = root_secrets->e(U_VALUES);
      // The node containing the w_values
      VHUtil::xml_node root_w = root_secrets->e(W_VALUES);
      // The node containing the a_values
      VHUtil::xml_node root_a = root_secrets->e(A_VALUES);
      
      auto_BN gamma = xml2BN(root_secrets->e(GAMMA)); // The value of gamma
      auto_BN nuu = xml2BN(root_secrets->e(NUU)); // The value of nu
      auto_BN tau_1 = xml2BN(root_secrets->e(TAU_1)); // The value of tau_1
      
      // Get the permutation out of xml
      std::ostringstream oss_perm; // A stream to hold the root_perm node
      oss_perm << *root_perm;
      // A vector of the permutation elements
      std::vector< int > perm_vec =
         get_permutation_vector_from_xml(oss_perm.str().c_str());

      auto_BN GValue; // A variable for GValue, a generator of gen
      VHInternal::fixed_mod_exp(GValue, gen, nuu, pm, ctx);
      add_BN_element(root_public, G_VALUE, GValue, DEC);

      auto_BN BigGamma; // A variable for BigGamma, which is G^gamma
      VHInternal::fixed_mod_exp(BigGamma, GValue, gamma, pm, ctx);
      add_BN_element(root_public, BIG_GAMMA, BigGamma, DEC);
      
      // The root node of xml_U
      VHUtil::xml_node root_U = root_public->new_element(U_VALUES);
      // The root node of xml_W
      VHUtil::xml_node root_W = root_public->new_element(W_VALUES);
      // The root node of xml_A
      VHUtil::xml_node root_A = root_public->new_element(A_VALUES);
      // The root node of xml_C
      VHUtil::xml_node root_C = root_public->new_element(C_VALUES);
      
      for (icount=0; icount<ksize; icount++)
      {
         auto_BN U_value; // The U value we will calculate
         auto_BN W_value; // The W value we will calculate
         auto_BN A_value; // The A value we will calculate
         auto_BN C_value; // The C value we will calculate
         
         auto_BN u_exp = xml2BN(root_u->e(icount));
         VHInternal::fixed_mod_exp(U_value, GValue,
                                   u_exp, pm, ctx);
         add_BN_element(root_U, U_VALUE, U_value, DEC);
         
         auto_BN tmp_exp;
         VH_nonzero(BN_mod_mul(tmp_exp, gamma, xml2BN(root_w->e(icount)), qm, ctx), BN_MOD_MUL);
         VHInternal::fixed_mod_exp(W_value, GValue, tmp_exp,
                                   pm, ctx);
         add_BN_element(root_W, W_VALUE, W_value, DEC);
         
         auto_BN a_exp = xml2BN(root_a->e(icount));
         VHInternal::fixed_mod_exp(A_value, GValue,
                                   a_exp, pm, ctx);
         add_BN_element(root_A, A_VALUE, A_value, DEC);
         
         int pval = perm_vec[icount]; // The permutation value at index icount
         // The a value at index pval
         auto_BN ap_value = xml2BN(root_a->e(pval-1));
         auto_BN exp_val; // The value of gamma*apvalue
         VH_nonzero(BN_mod_mul(exp_val, gamma, ap_value, qm, ctx), BN_MOD_MUL);
         VHInternal::fixed_mod_exp(C_value, GValue, exp_val,
                                   pm, ctx);
         add_BN_element(root_C, C_VALUE, C_value, DEC);
      }
      
      // Compute Lambda1 and Lambda2
      auto_BN Lambda_1;  // = (g^tau_1) * PROD[1-k] ( X_pi(i) ^ (w - u_pi(i)) )
      auto_BN Lambda_2;  // = (h^tau_1) * PROD[1-k] ( Y_pi(i) ^ (w - u_pi(i)) )
      
      // Calculate g and h parts first
      auto_BN g_raise_tau; // = g^tau_1
      auto_BN h_raise_tau; // = h^tau_1
      VHInternal::fixed_mod_exp(g_raise_tau, gen, tau_1, pm, ctx);
      VHInternal::fixed_mod_exp(h_raise_tau, ePublicKey, tau_1,
                                pm, ctx);
      
      // Now do loop
      auto_BN prod_value_1; // The running product of the X components
      VH_nonzero(BN_one(prod_value_1), BN_ONE);
      auto_BN prod_value_2; // The running product of the Y components
      VH_nonzero(BN_one(prod_value_2), BN_ONE);
      for (icount=0; icount<ksize; icount++)
      {
         int pval = perm_vec[icount]; // The permutation value at index icount
         // The value of X at index pval
         auto_BN Xp_value = xml2BN(root_Xvalues->e(pval-1));
         //VHUtil::cout() << "Xp_value for Lambda is " << Xp_value << std::endl;
         // The value of Y at index pval
         auto_BN Yp_value = xml2BN(root_Yvalues->e(pval-1));
         //VHUtil::cout() << "Yp_value for Lambda is " << Yp_value << std::endl;
         // The value of u at index pval
         auto_BN up_value = xml2BN(root_u->e(pval-1));
         
         auto_BN exp_value; // = w - u_pi_i
         VH_nonzero(BN_sub(exp_value, xml2BN(root_w->e(icount)), up_value), BN_SUB);
         exp_value.Canonicalize(qm);
         
         auto_BN entity_value_1; // = X^exp_value
         auto_BN entity_value_2; // = Y^exp_value
         VH_nonzero(BN_mod_exp(entity_value_1, Xp_value, exp_value, pm, ctx), BN_MOD_EXP);
         VH_nonzero(BN_mod_exp(entity_value_2, Yp_value, exp_value, pm, ctx), BN_MOD_EXP);
         
         // First time through tmp_prod_values are 1
         VH_nonzero(BN_mod_mul(prod_value_1, prod_value_1, entity_value_1, pm, ctx), BN_MOD_MUL);
         VH_nonzero(BN_mod_mul(prod_value_2, prod_value_2, entity_value_2, pm, ctx), BN_MOD_MUL);
      }
      VH_nonzero(BN_mod_mul(Lambda_1, g_raise_tau, prod_value_1, pm, ctx), BN_MOD_MUL);
      VH_nonzero(BN_mod_mul(Lambda_2, h_raise_tau, prod_value_2, pm, ctx), BN_MOD_MUL);
      add_BN_element(root_public, LAMBDA_1, Lambda_1, DEC);
      add_BN_element(root_public, LAMBDA_2, Lambda_2, DEC);
      std::ostringstream oss_public; // A stream to hold xml_public
      oss_public << xml_public;

      *public_shuffle_values = VHTI_dup(oss_public.str().c_str());
   }
   catch (const VHUtil::Exception & e)
   {
      VHTI_set_last_error(e);
      result = e.getResultNo();
   }
   return result;
}

int
VHInternal::generate_shuffle_hash_values(VHUtil::xml_tree &xml_bb,
                                         const char * X_hats,
                                         const char * Y_hats,
                                         const char *public_shuffle_values,
                                         const char * X_checks,
                                         const char * Y_checks,
                                         const char **rho_values)
{
   int result = 0; // Assume success until told otherwise
   int icount = 0; // A counter used for loops
   *rho_values = NULL;
   auto_BN pm(NULL); // The Election Modulus
   auto_BN qm(NULL); // The Election Subgroup Modulus
   auto_BN gen(NULL); // The Election Subgroup Generator
   auto_BN ePublicKey(NULL); // The Election Public Key
   
   try
   {  // An empty xml tree to hold the ShuffleHashValues
      VHUtil::xml_tree xml_hash("<ShuffleHashValues/>");
      VHUtil::xml_node root_hash = xml_hash.root(); // The root node of xml_hash
      VHInternal::get_election_parameters(xml_bb, pm,
         qm, gen, ePublicKey);
      
      // An xml tree from the public_shuffle_values input
      VHUtil::xml_tree xml_public(public_shuffle_values);
      // The root node of xml_public
      VHUtil::xml_node root_public = xml_public.root();
      
      VHUtil::xml_tree xml_Xvalues(X_hats); // An xml tree from the X_hats input
      // The root node of xml_Xvalues
      VHUtil::xml_node root_Xvalues = xml_Xvalues.root();
      VHUtil::xml_tree xml_Yvalues(Y_hats); // An xml tree from the Y_hats input
      // The root node of xml_Yvalues
      VHUtil::xml_node root_Yvalues = xml_Yvalues.root();
      int ksize = root_Xvalues->element_count(); // The number of ballots
      
      // An xml tree from the X_checks input
      VHUtil::xml_tree xml_Xvalues_shuf(X_checks);
      // The root node of xml_Xvalues_shuf
      VHUtil::xml_node root_Xbar = xml_Xvalues_shuf.root();
      // An xml tree from the Y_checks input
      VHUtil::xml_tree xml_Yvalues_shuf(Y_checks);
      // The root node of xml_Yvalues_shuf
      VHUtil::xml_node root_Ybar = xml_Yvalues_shuf.root();
      // The xml node containing the C values
      VHUtil::xml_node root_C = root_public->e(C_VALUES);
      // The xml node containing the A values
      VHUtil::xml_node root_A = root_public->e(A_VALUES);
      // The xml node containing the U values
      VHUtil::xml_node root_U = root_public->e(U_VALUES);
      // The xml node containing the W values
      VHUtil::xml_node root_W = root_public->e(W_VALUES);
       // The value of G
      auto_BN GValue   = xml2BN(root_public->e(G_VALUE));
      // The value of BigGamma
      auto_BN BigGamma = xml2BN(root_public->e(BIG_GAMMA));
      // The value of Lambda_1
      auto_BN Lambda_1 = xml2BN(root_public->e(LAMBDA_1));
      // The value of Lambda_2
      auto_BN Lambda_2 = xml2BN(root_public->e(LAMBDA_2));
      
      // Compute rho sequence, seeded from a hash of everything
      // An array to hold the values we are going to hash
      VHUtil::array< const BIGNUM * > arr1( 4 + 8*ksize );
      for (icount=0; icount<ksize; icount++) {
         arr1[icount] = xml2BN(root_Xvalues->e(icount));
      }
      for (icount=0; icount<ksize; icount++) {
         arr1[icount + ksize] = xml2BN(root_Yvalues->e(icount));
      }
      for (icount=0; icount<ksize; icount++) {
         arr1[icount + 2*ksize] = xml2BN(root_Xbar->e(icount));
      }
      for (icount=0; icount<ksize; icount++) {
         arr1[icount + 3*ksize] = xml2BN(root_Ybar->e(icount));
      }
      for (icount=0; icount<ksize; icount++) {
         arr1[icount + 4*ksize] = xml2BN(root_C->e(icount));
      }
      for (icount=0; icount<ksize; icount++) {
         arr1[icount + 5*ksize] = xml2BN(root_A->e(icount));
      }
      for (icount=0; icount<ksize; icount++) {
         arr1[icount + 6*ksize] = xml2BN(root_U->e(icount));
      }
      for (icount=0; icount<ksize; icount++) {
         arr1[icount + 7*ksize] = xml2BN(root_W->e(icount));
      }
      arr1[8*ksize] = GValue;
      arr1[8*ksize + 1] = BigGamma;
      arr1[8*ksize + 2] = Lambda_1;
      arr1[8*ksize + 3] = Lambda_2;
      
      // The hash of all of the values in the array
      auto_BN rho_hash_val = GetHashOfNBNs(arr1, arr1.m_size);
      add_BN_element(root_hash, "rho_hash_value", rho_hash_val, DEC);
      // The hash value represented as characters
      std::string key_str("<" RANDOM_SEED_KEY ">"); // String for RandomSeedKey xml
      {
         char * ch_rho_hash_val = BN_bn2dec(rho_hash_val);
         key_str += ch_rho_hash_val;
         OPENSSL_free(ch_rho_hash_val);
      }
      key_str += "</" RANDOM_SEED_KEY ">";

      // An empty xml tree to hold the rho values
      VHUtil::xml_tree xml_rho("<rho_values/>");
      VHUtil::xml_node root_rho = xml_rho.root(); // The root node of xml_rho
      auto_freeing<RandomState> random_state = 0; // The new random state
      VH_propagate(VHTI_generate_random_state(key_str.c_str(), &random_state),
         GENERATE_RANDOM_STATE);

      // A RandomState object
      VHInternal::RS rs (static_cast<RandomState>(random_state));
      for (icount=0; icount<ksize; icount++) {
         auto_BN rho; // A random rho value in q
         VHInternal::rand_range(qm, rs, rho);
         add_BN_element(root_rho, "rho_value", rho, DEC);
      }
      root_hash->add_element(root_rho->deep_copy());
      std::ostringstream oss_hash; // A stream to hold xml_hash
      oss_hash << xml_hash;
      *rho_values = VHTI_dup(oss_hash.str().c_str());
   }
   catch (const VHUtil::Exception & e) {
      VHTI_set_last_error(e);
      result = e.getResultNo();
   }
   return result;
}

int
VHInternal::generate_final_shuffle_values(VHUtil::xml_tree &xml_bb,
                                          const char *secret_shuffle_values,
                                          const char *rho_values,
                                          const char **final_shuffle_values,
                                          bool & collision)
{
   // Assume success until told otherwise
   int result = 0;
   // A counter used for loops
   int icount = 0;
   *final_shuffle_values = NULL;
   collision = false;
   // The Election Modulus
   auto_BN pm(NULL);
   // The Election Subgroup Modulus
   auto_BN qm(NULL);
   // The Election Subgroup Generator
   auto_BN gen(NULL);
   // The Election Public Key
   auto_BN ePublicKey(NULL);
   // An OpenSSL structure that holds BIGNUM temporary variables
   // used by library functions
   auto_BN_CTX ctx(BN_CTX_new());
   
   try {
      // An empty xml tree to hold the FinalShuffleValues
      VHUtil::xml_tree xml_final("<FinalShuffleValues/>");
      // The root node of xml_final
      VHUtil::xml_node root_final = xml_final.root();
      VHInternal::get_election_parameters(xml_bb,
         pm, qm, gen, ePublicKey);
      
      // Get rho, u, w, a, tao_0, beta, gamma out of xml
      // An xml tree from the rho_values input
      VHUtil::xml_tree xml_hash(rho_values);
      // The root node of xml_hash
      VHUtil::xml_node root_hash = xml_hash.root();
      // The node containing the rho_values
      VHUtil::xml_node root_rho = root_hash->e(RHO_VALUES);
      // The value of the single rho_hash_value
      auto_BN rho_hash_val = xml2BN(root_hash->e(RHO_HASH_VALUE));
      // An xml tree from the secret_shuffle_values input
      VHUtil::xml_tree xml_secrets(secret_shuffle_values);
      // The root node of xml_secrets
      VHUtil::xml_node root_secrets = xml_secrets.root();
      // The xml node containing the permutation
      VHUtil::xml_node root_perm = root_secrets->e(PERMUTATION);
      // The xml node containing the beta values
      VHUtil::xml_node root_beta = root_secrets->e(BETA_VALUES);
      // The xml node containing the u values
      VHUtil::xml_node root_u = root_secrets->e(U_VALUES);
      // The xml node containing the w values
      VHUtil::xml_node root_w = root_secrets->e(W_VALUES);
      // The xml node containing the a values
      VHUtil::xml_node root_a = root_secrets->e(A_VALUES);
      // The number of ballots
      int ksize = root_u->element_count();
      // The value of nu
      auto_BN nuu   = xml2BN(root_secrets->e(NUU));
      // The value of gamma
      auto_BN gamma = xml2BN(root_secrets->e(GAMMA));
      // The value of tau_0
      auto_BN tau_0 = xml2BN(root_secrets->e(TAU_0));
      
      std::ostringstream oss_perm;  // Get the permutation out of xml
      oss_perm << *root_perm;
      // A vector to hold the permutation values
      std::vector< int > perm_vec =
         get_permutation_vector_from_xml(oss_perm.str().c_str());

      // Calculate GValue
      auto_BN GValue;
      VHInternal::fixed_mod_exp(GValue, gen, nuu, pm, ctx);
      
      // Calculate b, d, and D sequences
      // A vector to hold the b values
      std::vector< auto_BN > b_vec;
      // A vector to hold the d values
      std::vector< auto_BN > d_vec;
      // A vector to hold thd D values
      std::vector< auto_BN > D_vec;
      // A set to make sure the b values are unique
      std::set< auto_BN > b_set;
      for (icount=0; icount<ksize; icount++) {
         // The b value we will calculate
         auto_BN b_value;
         VH_nonzero(BN_sub(b_value, xml2BN(root_rho->e(icount)),
                           xml2BN(root_u->e(icount)) ), BN_SUB);
         if ( (b_set.end() == b_set.find(b_value)) && !(BN_is_zero(b_value)) )
         {
            b_value.Canonicalize(qm);
            b_vec.push_back(b_value);
            b_set.insert(b_value);
         }
         else
         {
            collision = true;
            VHUtil::cout() << "Retry because b is not unique or is zero" << std::endl;
         }
      }
      
      if (collision == false)
      {
         for (icount=0; icount<ksize; icount++) {
            // The d value we will calculate
            auto_BN d_value;
            // The D value we will calculate
            auto_BN D_value;
            // The value of the permutation at index icount
            int pval = perm_vec[icount];
            // The b value at inde pval
            auto_BN bp_value = b_vec[pval-1];
            VH_nonzero(BN_mod_mul(d_value, gamma, bp_value, qm, ctx), BN_MOD_MUL);
            d_vec.push_back(d_value);
            VHInternal::fixed_mod_exp(D_value, GValue,
                                      d_value, pm, ctx);
            D_vec.push_back(D_value);
         }
         
         // Now hash the D values with the previous hash
         // An array to hold the values to hash
         VHUtil::array< const BIGNUM * > arr2( ksize+1 );
         arr2[0] = rho_hash_val;
         for (icount=1; icount<ksize+1; icount++) {
            arr2[icount] = D_vec[icount-1];
         }
         // The value of the hash of the array elements
         auto_BN lambda_value = GetHashOfNBNs(arr2, arr2.m_size);
         
         // Calculate r sequence
         // A set to make sure the r values are unique
         std::set< auto_BN > r_set;
         // An empty xml tree to hold the r values
         VHUtil::xml_tree xml_rvalues("<r_values/>");
         // The root node of xml_rvalues
         VHUtil::xml_node root_rvalues = xml_rvalues.root();
         for (icount=0; icount<ksize; icount++) {
            // The r value we will calculate
            auto_BN r_value;
            // An auto_BN to hold lambda*b
            auto_BN tmp_mul;
            VH_nonzero(BN_mod_mul(tmp_mul, lambda_value, b_vec[icount], qm, ctx), BN_MOD_MUL);
            VH_nonzero(BN_add(r_value, xml2BN(root_a->e(icount)), tmp_mul), BN_ADD);
            if ( (r_set.end() == r_set.find(r_value)) && !(BN_is_zero(r_value)) )
            {
               r_value.Canonicalize(qm);
               add_BN_element(root_rvalues, "rvalue", r_value);
               r_set.insert(r_value);
            }
            else
            {
               collision = true;
               VHUtil::cout() << "Retry because r is not unique or is zero" << std::endl;
               // Note: I don't see how r could ever be zero given our Canonicalization
               // and the fact that neither a nor b can be zero.  But it's good to check.
            }
         }
         
         if (collision == false)
         {
            root_final->add_element(root_rvalues->deep_copy());
            
            // Calculate sigma sequence: sigma = w_i + b_pi_i
            // An empty xml tree to hold the sigma values
            VHUtil::xml_tree xml_sigma("<sigma_values/>");
            // The root node of xml_sigma
            VHUtil::xml_node root_sigma = xml_sigma.root();
            for (icount=0; icount<ksize; icount++) {
               // The value of the permutation at index icount
               int pval = perm_vec[icount];
               // The sigma value we will calculate
               auto_BN sigma_value;
               // The b value at index pval
               auto_BN bp_value = b_vec[pval-1];
               VH_nonzero(BN_add(sigma_value, xml2BN(root_w->e(icount)), bp_value), BN_ADD);
               sigma_value.Canonicalize(qm);
               add_BN_element(root_sigma, SIGMA, sigma_value, DEC);
            }
            
            // Add into FinalShuffleValues
            root_final->add_element(root_sigma->deep_copy());
            
            auto_BN tau;  // The tau value we will calculate
            auto_BN tau_sum_value; // The sum of the b*beta products
            VH_nonzero(BN_zero(tau_sum_value), BN_ZERO);
            for (icount=0; icount<ksize; icount++) {
               // The product of b and beta
               auto_BN mul_value;
               VH_nonzero(BN_mod_mul(mul_value, b_vec[icount],
                                     xml2BN(root_beta->e(icount)), qm, ctx), BN_MOD_MUL);
               VH_nonzero(BN_add(tau_sum_value, tau_sum_value, mul_value), BN_ADD);
               tau_sum_value.Canonicalize(qm);
            }
            VH_nonzero(BN_sub(tau, tau_sum_value, tau_0), BN_SUB);
            tau.Canonicalize(qm);
            add_BN_element(root_final, TAU, tau, DEC);
            // A stream to hold xml_final
            std::ostringstream oss_final;
            oss_final << xml_final;
            *final_shuffle_values = VHTI_dup(oss_final.str().c_str());
         }
      }
   }
   catch (const VHUtil::Exception & e)
   {
      VHTI_set_last_error(e);
      result = e.getResultNo();
   }
   return result;
}

int
VHInternal::simple_k_shuffle
(VHUtil::xml_tree &xml_bb,
 const char *xvalues,
 const char *gamma_val,
 Permutation permutation,
 const char *nuu_val,
 RandomState random_state,
 SimpleShuffleValidityProof *simple_shuffle_validity_proof, // "Long" version
 RandomState *random_state_out,
 bool & collision)
{
   int result = 0; // Assume success until told otherwise
   *simple_shuffle_validity_proof = NULL;
   *random_state_out = NULL;
   collision = false;
   int icount = 0; // A counter used for loops
   auto_BN pm(NULL); // The Election Modulus
   auto_BN qm(NULL); // The Election Subgroup Modulus
   auto_BN gen(NULL); // The Election Subgroup Generator
   auto_BN ePublicKey(NULL); // The Election Public Key
   // An OpenSSL structure that holds BIGNUM temporary variables
   // used by library functions
   auto_BN_CTX ctx(BN_CTX_new());
   
   try
   {
      VHInternal::RS rs (random_state); // A RandomState object
      // Make empty ShuffleValidityProof object
      VHUtil::xml_tree xml_svp("<" SIMPLE_SHUFFLE_VALIDITY_PROOF "/>");
      VHUtil::xml_node root_svp = xml_svp.root(); // The root node of xml_svp
      
      VHInternal::get_election_parameters(xml_bb, pm,
         qm, gen, ePublicKey);
      
      // Get x values out of XML, put into vector
      std::vector< auto_BN > x_vec;
      VHUtil::xml_tree xml_xvalues(xvalues); // An xml tree from xvalues input
      // The root node of xml_xvalues
      VHUtil::xml_node root_xvalues = xml_xvalues.root();
      int ksize = root_xvalues->element_count(); // The number of ballots
      for (icount=0; icount<ksize; icount++)
      {
         x_vec.push_back(xml2BN(root_xvalues->e(icount)));
      }
      std::ostringstream k_oss; // A stream to hold ksize
      k_oss << ksize;
      
      VHUtil::xml_tree xml_gamma(gamma_val); // Get gamma and nu out of XML
      auto_BN gamma = xml2BN(xml_gamma.root()); // The value of gamma
      VHUtil::xml_tree xml_nu(nuu_val); // An xml tree from the nu input
      auto_BN nuu = xml2BN(xml_nu.root()); // The value of nu

      auto_BN GValue; // Generate G_value from nu
      VHInternal::fixed_mod_exp(GValue, gen, nuu, pm, ctx);
      add_BN_element(root_svp, G_VALUE, GValue, DEC);
      
      // Calculate (BigGamma = GValue^gamma) and put into
      // your SimpleShuffleValidityProof xml
      auto_BN BigGamma;
      VHInternal::fixed_mod_exp(BigGamma, GValue, gamma, pm,
                                ctx);
      add_BN_element(root_svp, BIG_GAMMA, BigGamma, DEC);

      // A vector to hold the permutation values
      std::vector< int > perm_vec
         = VHInternal::get_permutation_vector_from_xml(permutation);

      // Compute the big X values from the x values
      std::vector< auto_BN > X_vec; // A vector to hold the X values
      for (icount=0; icount<ksize; icount++)
      {
         auto_BN X_value; // The X value we will calculate
         VHInternal::fixed_mod_exp(X_value, GValue,
                                   x_vec[icount], pm, ctx);
         X_vec.push_back(X_value);
      }
      
      // Calculate Y values from X values
      std::vector< auto_BN > Y_vec; // A vector to hold the Y values
      for (icount=0; icount<ksize; icount++)
      {
         int pval = perm_vec[icount]; // The permutation value at index icount
         // Get Pi(ith) value out of vector of Xs
         auto_BN Xp_value = X_vec[pval-1];
         auto_BN Y_value; // The Y value we will calculate
         VHInternal::fixed_mod_exp(Y_value, Xp_value, gamma,
                                   pm, ctx);
         Y_vec.push_back(Y_value);
      }
      
      // Now you have everything you need to calculate
      // t = Hash( G_value, BigGamma, {X_i}, {Y_i} )
      // An array to hold values to hash
      VHUtil::array< const BIGNUM * > arr1( 2 + 2*ksize );
      arr1[0] = GValue;
      arr1[1] = BigGamma;
      
      // Now append the other items
      int arr_index1 = 2; // The index of the array
      for (icount=0; icount<ksize; icount++) {
         arr1[arr_index1] = X_vec[icount];
         arr_index1++;
      }
      for (icount=0; icount<ksize; icount++) {
         arr1[arr_index1] = Y_vec[icount];
         arr_index1++;
      }
      // The hash of all the elements in the array
      auto_BN t_hash = GetHashOfNBNs(arr1, arr1.m_size);
      t_hash.Canonicalize(qm);

      for (icount=0; icount<x_vec.size(); icount++)
      {
         if (BN_cmp(x_vec[icount], t_hash) == 0)
         {
            // This will probably never happen using real-world numbers
            // But it is good to check, and it means that somebody got
            // lucky guessing secrets
            collision = true;
            VHUtil::cout() << "  Retry because x=t_hash" << std::endl;
         }
      }
      
      if (collision == false)
      {
         // Now that we have t we can get the xbar values
         std::vector< auto_BN > xbar_vec; // A vector to hold xbar values
         for (icount=0; icount<ksize; icount++)
         {
            auto_BN xbar; // The xbar value we will calculate
            VH_nonzero(BN_sub(xbar, x_vec[icount], t_hash), BN_SUB);
            xbar.Canonicalize(qm);
            xbar_vec.push_back(xbar);
         }
         for (icount=ksize; icount<ksize*2; icount++) {
            xbar_vec.push_back(gamma);
         }
         
         // From the xbar values we can get the ybar values (needed for alphas)
         std::vector< auto_BN > ybar_vec; // A vector to hold ybar values
         for (icount=0; icount<ksize; icount++)
         {
            int pval = perm_vec[icount]; // Permutation value at index icount
            // Get Pi(ith) value out of vector of Xs
            auto_BN xbar = xbar_vec[pval-1];
            auto_BN ybar; // The ybar value we will calculate
            VH_nonzero(BN_mod_mul(ybar, xbar, gamma, qm, ctx), BN_MOD_MUL);
            ybar_vec.push_back(ybar);
         }
         for (icount=ksize; icount<ksize*2; icount++)
         {
            auto_BN one_bn; // An auto_BN with the value of 1
            VH_nonzero(BN_one(one_bn), BN_ONE);
            ybar_vec.push_back(one_bn);
         }
         
         // Compute secret random thetas in Zq
         std::vector< auto_BN > tht_vec; // A vector to hold the theta values
         for (icount=0; icount<(2*ksize-1); icount++)
         {
            auto_BN tht(NULL); // The theta value we will calculate
            VHInternal::rand_range(qm, rs, tht);
            tht_vec.push_back(tht);
         }
         
         // Compute the Theta values (formerly A values)
         // The root node of xml_Thetas
         VHUtil::xml_node root_Thetas = root_svp->new_element(THETA_VALUES);
         std::vector< auto_BN > Theta_vec; // A vector to hold the Theta values
         for (icount=0; icount<ksize; icount++)
         {
            auto_BN prod1; // The xbar component
            auto_BN prod2; // The ybar component
            auto_BN exp_value; // prod1 - prod2
            auto_BN Theta_value; // The Theta we will end up with
            
            if (icount == 0)
            {
               VH_nonzero(BN_zero(prod1), BN_ZERO);
               VH_nonzero(BN_mod_mul(prod2, tht_vec[icount], ybar_vec[icount], qm, ctx), BN_MOD_MUL);
            }
            else
            {
               VH_nonzero(BN_mod_mul(prod1, tht_vec[icount-1], xbar_vec[icount], qm, ctx), BN_MOD_MUL);
               VH_nonzero(BN_mod_mul(prod2, tht_vec[icount], ybar_vec[icount], qm, ctx), BN_MOD_MUL);
            }
            
            VH_nonzero(BN_sub(exp_value, prod1, prod2), BN_SUB);
            exp_value.Canonicalize(qm);
            VHInternal::fixed_mod_exp(Theta_value, GValue,
                                      exp_value, pm, ctx);
            // For long proof
            add_BN_element(root_Thetas, THETA_VALUE, Theta_value);
            Theta_vec.push_back(Theta_value);
         }
         for (icount=ksize; icount<2*ksize; icount++)
         {
            auto_BN prod; // gamma * theta
            auto_BN exp_value; // prod - theta
            auto_BN Theta_value; // The Theta we will end up with
            if ( icount == (2*ksize-1) ) {
               VH_nonzero(BN_mod_mul(exp_value, gamma, tht_vec[icount-1], qm, ctx), BN_MOD_MUL);
            }
            else {
               VH_nonzero(BN_mod_mul(prod, gamma, tht_vec[icount-1], qm, ctx), BN_MOD_MUL);
               VH_nonzero(BN_sub(exp_value, prod, tht_vec[icount]), BN_SUB);
               exp_value.Canonicalize(qm);
            }
            VHInternal::fixed_mod_exp(Theta_value, GValue,
                                      exp_value, pm, ctx);
            // For long proof
            add_BN_element(root_Thetas, THETA_VALUE, Theta_value);
            Theta_vec.push_back(Theta_value);
         }
        
         // Now that you have {Theta} you can compute c_hash
         // c_hash = H(G_value, BigGamma, {X}, {Y}, {Theta});
         // An array to hold all of the elements to hash
         VHUtil::array< const BIGNUM * > arr2( 2 + ksize + ksize + 2*ksize);
         for (icount=0; icount<arr1.m_size; icount++) {
            arr2[icount] = arr1[icount];
         }
         
         // Now append the Theta values
         int arr_index2 = arr1.m_size; // The index of the array
         for (icount=0; icount<2*ksize; icount++)
         {
            arr2[arr_index2] = Theta_vec[icount];
            arr_index2++;
         }
         // The hash of all the array elements
         auto_BN c_hash = GetHashOfNBNs(arr2, arr2.m_size);
         c_hash.Canonicalize(qm);
         
         // Add this to your SimpleShuffleValidityProof object
         // add_BN_element(root_svp, C_HASH, c_hash, DEC);  // For short proof
         
         // Now finally we need to calculate our alphas
         // EASY WAY
         std::vector< auto_BN > alpha_vec; // A vector to hold the alpha values
         auto_BN total_product;  // Store value so you don't repeat calculations
         VH_nonzero(BN_one(total_product), BN_ONE);
         for (icount=0; icount<(2*ksize-1); icount++)
         {
            auto_BN alpha_value; // The alpha value we will calculate
            auto_BN current_product; // The running product
            if (icount < ksize)
            {
               auto_BN ybar_inv; // The inverse of ybar
               VH_nonzero(BN_mod_inverse(ybar_inv, ybar_vec[icount], qm, ctx), BN_MOD_INVERSE);
               VH_nonzero(BN_mod_mul(current_product, xbar_vec[icount], ybar_inv, qm, ctx), BN_MOD_MUL);
            }
            else {
               current_product = gamma;
            }

            if (icount == 0) {
               total_product = current_product;
            }
            else {
               VH_nonzero(BN_mod_mul(total_product, total_product, current_product, qm,
                                     ctx), BN_MOD_MUL);
            }

            auto_BN tmp_prod; // total_product * c_hash
            VH_nonzero(BN_mod_mul(tmp_prod, c_hash, total_product, qm, ctx), BN_MOD_MUL);

            VH_nonzero(BN_add(alpha_value, tht_vec[icount], tmp_prod), BN_ADD);
            alpha_value.Canonicalize(qm);
            alpha_vec.push_back(alpha_value);
         }
         // An empty xml tree to hold the alpha values
         VHUtil::xml_tree xml_alphas("<alpha_values/>");
         // The root node of xml_alphas
         VHUtil::xml_node root_alphas = xml_alphas.root();
         for (icount=0; icount<(2*ksize-1); icount++)
         {
            VHUtil::xml_node alpha_node = add_BN_element(root_alphas, ALPHA,
               alpha_vec[icount], DEC);
         }
         // END OF EASY WAY
         

         /*--- HARD WAY
         std::vector< auto_BN > tmp_alpha_vec;
         auto_BN last_product;  // Store value so you don't repeat calculations
         VH_nonzero(BN_one(last_product), BN_ONE);
         for (icount=(2*ksize-2); icount >=0; icount--)
         {
            auto_BN alpha_value;
            auto_BN xbar_inv;
            VH_nonzero(BN_mod_inverse(xbar_inv, xbar_vec[icount+1],
         qm, ctx), BN_MOD_INVERSE);
            
            auto_BN current_product;
            auto_BN total_product;
            VH_nonzero(BN_mod_mul(current_product, ybar_vec[icount+1],
            xbar_inv, qm, ctx), BN_MOD_MUL);
            
            if (icount == (2*ksize-2))
            {
               total_product = current_product;
            }
            else
            {
               VH_nonzero(BN_mod_mul(total_product, last_product, current_product, qm,
                          ctx), BN_MOD_MUL);
            }
            
            auto_BN tmp_prod;
            VH_nonzero(BN_mod_mul(tmp_prod, c_hash, total_product, qm,
            ctx), BN_MOD_MUL);
            
            VH_nonzero(BN_add(alpha_value, tht_vec[icount], tmp_prod),
            BN_ADD);
            alpha_value.Canonicalize(qm);
            tmp_alpha_vec.push_back(alpha_value);
            last_product = total_product;
         }
         
         // Since these alphas are in reverse order,
         // need to put them in correct order
         std::vector< auto_BN > alpha_vec;
         VHUtil::xml_tree xml_alphas("<alpha_values/>");
         VHUtil::xml_node root_alphas = xml_alphas.root();
         for (icount=(2*ksize-2); icount >=0; icount--)
         {
            alpha_vec.push_back(tmp_alpha_vec[icount]);
         }
         
         for (icount=0; icount<(2*ksize-1); icount++)
         {
            std::ostringstream count_oss;
            count_oss << icount;
            VHUtil::xml_node alpha_node = add_BN_element(root_alphas, ALPHA,
               alpha_vec[icount], DEC);
         }
         // END OF HARD WAY  */

         // Insert the alpha values into the simple shuffle validity proof
         root_svp->add_element(root_alphas->deep_copy());

         // A stream to hold xml_svp
         std::ostringstream svp_stream;
         svp_stream << xml_svp;
         *simple_shuffle_validity_proof = VHTI_dup(svp_stream.str().c_str());
         *random_state_out = VHTI_dup (rs);
      }
   }
   catch (const VHUtil::Exception & e) {
      VHTI_set_last_error(e);
      result = e.getResultNo();
   }
   return result;
}
