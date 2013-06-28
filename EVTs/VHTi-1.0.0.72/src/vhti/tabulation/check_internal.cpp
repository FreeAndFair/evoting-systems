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
#include <tabulation/tabulation_internal.h>
#include <tabulation/check_internal.h>
#include <tabulation/shuffle_internal.h>
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
VHInternal::generate_simple_check_inputs
(VHUtil::xml_tree &xml_bb,
 ShuffleValidityProof shuffle_validity_proof,
 const char *rho_values,
 const char **RValues,
 const char **SValues)
{
   int result = 0; // Assume success until told otherwise
   int icount = 0; // A counter used for loops
   *RValues = NULL;
   *SValues = NULL;
   auto_BN pm(NULL); // The Election Modulus
   auto_BN qm(NULL); // The Election Subgroup Modulus
   auto_BN gen(NULL); // The Election Subgroup Generator
   auto_BN ePublicKey(NULL); // The Election Public Key
   // An OpenSSL structure that holds BIGNUM temporary variables
   // used by library functions
   auto_BN_CTX ctx(BN_CTX_new());
   
   try {
      VHInternal::get_election_parameters(xml_bb, pm, qm,
         gen, ePublicKey);
      
      // An xml tree from the rho_values input
      VHUtil::xml_tree xml_hash(rho_values);
      VHUtil::xml_node root_hash = xml_hash.root(); // The root node of xml_hash
      // The root node of the multiple rho values
      VHUtil::xml_node root_rho = root_hash->e(RHO_VALUES);
      // The value of the single rho hash value
      auto_BN rho_hash_val = xml2BN(root_hash->e(RHO_HASH_VALUE));
      // An xml tree from the shuffle_validity_proof input
      VHUtil::xml_tree xml_svp(shuffle_validity_proof);
      VHUtil::xml_node root_svp = xml_svp.root(); // The root node of xml_svp
      // The node containing the SimpleShuffleValidityProof
      VHUtil::xml_node node_ssvp = root_svp->e(SIMPLE_SHUFFLE_VALIDITY_PROOF);
      // The node containing the C values
      VHUtil::xml_node root_C = root_svp->e(C_VALUES);
      // The node containing the A values
      VHUtil::xml_node root_A = root_svp->e(A_VALUES);
      // The node containing the U values
      VHUtil::xml_node root_U = root_svp->e(U_VALUES);
      // The node containing the W values
      VHUtil::xml_node root_W = root_svp->e(W_VALUES);
      // The node containing the sigma values
      VHUtil::xml_node root_sigma = root_svp->e(SIGMA_VALUES);
      // The value of G, a generator of gen
      auto_BN GValue = xml2BN(node_ssvp->e(G_VALUE));
      // The value of G^gamma
      auto_BN BigGamma = xml2BN(node_ssvp->e(BIG_GAMMA));
      // Number of ballots (could have been determined from other data as well)
      int ksize = root_W->element_count();
      
      // Calculate D sequence:     D = (BigGamma^sigma) / W
      std::vector< auto_BN > D_vec; // A vector to hold the D values
      for (icount=0; icount<ksize; icount++)
      {
         auto_BN D_value; // The D value we are going to calculate
         auto_BN tmp_exp; // A variable to hold BigGamma^sigma
         auto_BN sigma_exp = xml2BN(root_sigma->e(icount));
         VHInternal::fixed_mod_exp(tmp_exp, BigGamma,
                                   sigma_exp, pm, ctx);
         auto_BN W_inverse; // A variable to hold the inverse of W
         VH_nonzero (BN_mod_inverse(W_inverse, xml2BN(root_W->e(icount)), pm, ctx), BN_MOD_INVERSE);
         VH_nonzero(BN_mod_mul(D_value, tmp_exp, W_inverse, pm, ctx), BN_MOD_MUL);
         D_vec.push_back(D_value);
      }
      
      // Calculate lambda, which is hash of rho and D sequence
      // An array consisiting of the rho_hash_val and all of the D values
      VHUtil::array< const BIGNUM * > arr2( ksize+1 );
      arr2[0] = rho_hash_val;
      for (icount=1; icount<ksize+1; icount++) {
         arr2[icount] = D_vec[icount-1];
      }
      // A variable to hold the hash of our array elements
      auto_BN lambda_value = GetHashOfNBNs(arr2, arr2.m_size);
      
      // Calculate B sequence:     B = (GValue^rho) / U
      std::vector< auto_BN > B_vec; // A vector to hold the B values
      for (icount=0; icount<ksize; icount++)
      {
         auto_BN B_value; // The B value we are going to calculate
         auto_BN tmp_exp; // A variable to hold GValue^rho
         auto_BN rho_exp = xml2BN(root_rho->e(icount));
         VHInternal::fixed_mod_exp(tmp_exp, GValue,
                                   rho_exp, pm, ctx);
         auto_BN U_inverse; // A variable to hold the inverse of U
         VH_nonzero(BN_mod_inverse(U_inverse, xml2BN(root_U->e(icount)), pm, ctx), BN_MOD_INVERSE);
         VH_nonzero(BN_mod_mul(B_value, tmp_exp, U_inverse, pm, ctx), BN_MOD_MUL);
         B_vec.push_back(B_value);
      }
      
      // Calculate R and S sequences
      // R = A*(B^lambda),   S = C*(D^lambda)
      // An empty xml tree for the R values we will calculate
      VHUtil::xml_tree xml_R("<R_Values/>");
      VHUtil::xml_node root_R = xml_R.root(); // The root node of xml_R
      // An empty xml tree for the S values we will calculate
      VHUtil::xml_tree xml_S("<S_Values/>");
      VHUtil::xml_node root_S = xml_S.root(); // The root node of xml_S
      for (icount=0; icount<ksize; icount++)
      {
         auto_BN R_value; // The R value we are going to calculate
         auto_BN tmp_exp1; // A variable to hold B^lambda
         VH_nonzero(BN_mod_exp(tmp_exp1, B_vec[icount], lambda_value, pm, ctx), BN_MOD_EXP);
         VH_nonzero(BN_mod_mul(R_value, xml2BN(root_A->e(icount)), tmp_exp1, pm, ctx), BN_MOD_MUL);
         add_BN_element(root_R, "R_Value", R_value, DEC);
         auto_BN S_value; // The S value we are going to calculate
         auto_BN tmp_exp2; // A variable to hold D^lambda
         VH_nonzero(BN_mod_exp(tmp_exp2, D_vec[icount], lambda_value, pm, ctx), BN_MOD_EXP);
         VH_nonzero(BN_mod_mul(S_value, xml2BN(root_C->e(icount)), tmp_exp2, pm, ctx), BN_MOD_MUL);
         add_BN_element(root_S, "S_Value", S_value, DEC);
      }
      std::ostringstream oss_RValues; // A stream to contain the R values
      oss_RValues << xml_R;
      std::ostringstream oss_SValues; // A stream to contain the S values
      oss_SValues << xml_S;
      *RValues = VHTI_dup(oss_RValues.str().c_str());
      *SValues = VHTI_dup(oss_SValues.str().c_str());;
   }
   catch (const VHUtil::Exception & e) {
      VHTI_set_last_error(e);
      result = e.getResultNo();
   }
   return result;
}

int
VHInternal::check_values(VHUtil::xml_tree &xml_bb,
                         const char *Xvalues_before,
                         const char *Yvalues_before,
                         const char *Xvalues_after,
                         const char *Yvalues_after,
                         const char *rho_values,
                         ShuffleValidityProof shuffle_validity_proof,
                         CheckResults *check_shuffle_answer_result)
{
   int result = 0; // Assume success until told otherwise
   int icount = 0; // A counter used for loops
   *check_shuffle_answer_result = NULL;
   auto_BN pm(NULL); // The Election Modulus
   auto_BN qm(NULL); // The Election Subgroup Modulus
   auto_BN gen(NULL); // The Election Subgroup Generator
   auto_BN ePublicKey(NULL); // The Election Public Key
   // An OpenSSL structure that holds BIGNUM temporary variables
   // used by library functions
   auto_BN_CTX ctx(BN_CTX_new());
   
   try
   {  // An empty xml tree for the CheckResults we will create
      VHUtil::xml_tree xml_res("<" CHECK_RESULTS "/>");
      VHUtil::xml_node root_res = xml_res.root(); // The root node of xml_res
      VHInternal::get_election_parameters(xml_bb,
         pm, qm, gen, ePublicKey);
      
      // An xml tree from the Xvalues_before input
      VHUtil::xml_tree xml_Xb(Xvalues_before);
      VHUtil::xml_node root_Xb = xml_Xb.root(); // The root node of xml_Xb
      // An xml tree from the Yvalues_before input
      VHUtil::xml_tree xml_Yb(Yvalues_before);
      VHUtil::xml_node root_Yb = xml_Yb.root(); // The root node of xml_Yb
      // An xml tree from the Xvalues_after input
      VHUtil::xml_tree xml_Xa(Xvalues_after);
      VHUtil::xml_node root_Xa = xml_Xa.root(); // The root node of xml_Xa
      // An xml tree from the Yvalues_after input
      VHUtil::xml_tree xml_Ya(Yvalues_after);
      VHUtil::xml_node root_Ya = xml_Ya.root(); // The root node of xml_Ya
      // Number of ballots (could have been determined from other data as well)
      int ksize = root_Xb->element_count();
      
      // An xml tree from the shuffle_validity_proof input
      VHUtil::xml_tree xml_svp(shuffle_validity_proof);
      VHUtil::xml_node root_svp = xml_svp.root(); // The root node of xml_svp
      // The node containing the sigma values
      VHUtil::xml_node root_sigma = root_svp->e(SIGMA_VALUES);
      // The value of proof variable Lambda_1
      auto_BN Lambda_1 = xml2BN(root_svp->e(LAMBDA_1));
      // The value of proof variable Lambda_2
      auto_BN Lambda_2 = xml2BN(root_svp->e(LAMBDA_2));
      auto_BN tau = xml2BN(root_svp->e(TAU)); // Value of proof variable tau
      
      VHUtil::xml_tree xml_hash(rho_values); // xml tree from rho_values input
      VHUtil::xml_node root_hash = xml_hash.root(); // The root node of xml_hash
      // The root node of the multiple rho values
      VHUtil::xml_node root_rho = root_hash->e(RHO_VALUES);
      
      // Phi1 = PROD( (Xshuf^sigma) * (X^(-rho)) )
      // Phi2 = PROD( (Yshuf^sigma) * (Y^(-rho)) )
      auto_BN total_X_product; // The final product of the X components
      VH_nonzero(BN_one(total_X_product), BN_ONE);
      auto_BN total_Y_product; // The final product of the Y components
      VH_nonzero(BN_one(total_Y_product), BN_ONE);
      for (icount=0; icount<ksize; icount++) {
         auto_BN current_X_product; // The current product of the X components
         auto_BN current_Y_product; // The current product of the Y components
         auto_BN exp_x1; // A variable to hold Xa^sigma
         auto_BN exp_x2; // A variable to hold Xb^(-rho)
         auto_BN exp_y1; // A variable to hold Ya^sigma
         auto_BN exp_y2; // A variable to hold Yb^(-rho)
         auto_BN minus_rho; // need -rho = q-rho
         VH_nonzero(BN_sub(minus_rho, qm, xml2BN(root_rho->e(icount))), BN_SUB);
         minus_rho.Canonicalize(qm);
         
         VH_nonzero(BN_mod_exp(exp_x1, xml2BN(root_Xa->e(icount)),
                               xml2BN(root_sigma->e(icount)), pm, ctx), BN_MOD_EXP);
         VH_nonzero(BN_mod_exp(exp_x2, xml2BN(root_Xb->e(icount)),
                               minus_rho, pm, ctx), BN_MOD_EXP);
         VH_nonzero(BN_mod_exp(exp_y1, xml2BN(root_Ya->e(icount)),
                               xml2BN(root_sigma->e(icount)), pm, ctx), BN_MOD_EXP);

         VH_nonzero(BN_mod_exp(exp_y2, xml2BN(root_Yb->e(icount)), minus_rho, pm, ctx), BN_MOD_EXP);
         VH_nonzero(BN_mod_mul(current_X_product, exp_x1, exp_x2, pm, ctx), BN_MOD_MUL);
         VH_nonzero(BN_mod_mul(current_Y_product, exp_y1, exp_y2, pm, ctx), BN_MOD_MUL);
         
         VH_nonzero(BN_mod_mul(total_X_product, total_X_product, current_X_product,
                               pm, ctx), BN_MOD_MUL);
         VH_nonzero(BN_mod_mul(total_Y_product, total_Y_product, current_Y_product,
                               pm, ctx), BN_MOD_MUL);
      }
      auto_BN Phi_1 = total_X_product; // Check Phi_1 against proof
      auto_BN Phi_2 = total_Y_product; // Check Phi_2 against proof
      
      auto_BN tmp_exp; // A variable to hold g^tau
      VHInternal::fixed_mod_exp(tmp_exp, gen, tau, pm,
                                ctx);
      auto_BN lhs; // A variable for Lambda_1*tmp_exp
      VH_nonzero(BN_mod_mul(lhs, Lambda_1, tmp_exp, pm, ctx), BN_MOD_MUL);
      result = BN_cmp(lhs, Phi_1);  // Check that Lambda1 * g^tau = Phi1;
      if (result != 0) {
         root_res->add_characters(CHECK_FAILURE_TEXT);
         VHUtil::cout() << "Phi1 Check Failed in CheckShuffle" << std::endl;
      }

      if (result == 0)
      {  // Check that Lambda2 * h^tau = Phi2;
         auto_BN tmp_exp2; // A variable to hold h^tau
         VHInternal::fixed_mod_exp(tmp_exp2, ePublicKey, tau,
                                   pm, ctx);
         auto_BN lhs2; // A variable for Lambda_2*tmp_exp2
         VH_nonzero(BN_mod_mul(lhs2, Lambda_2, tmp_exp2, pm, ctx), BN_MOD_MUL);
         result = BN_cmp(lhs2, Phi_2);
         if (result != 0) {
            root_res->add_characters(CHECK_FAILURE_TEXT);
            VHUtil::cout() << "Phi2 Check Failed in CheckShuffle" << std::endl;
         }
      }
      
      if (result == 0) {
         root_res->add_characters(CHECK_SUCCESS_TEXT);
      }
      else {
         root_res->add_characters(CHECK_FAILURE_TEXT);
         VHUtil::cout() << "Unknown failure in CheckShuffle" << std::endl;
      }
      std::ostringstream res_stream;  // A stream to contain the results xml
      res_stream << xml_res;
      *check_shuffle_answer_result = VHTI_dup(res_stream.str().c_str());
   }
   catch (const VHUtil::Exception & e) {
      VHTI_set_last_error(e);
      result = e.getResultNo();
   }
   return result;
}

int
VHInternal::check_shuffle_el_gamal_sequence
(VHUtil::xml_tree &xml_bb,
 const char *Xvalues_before,
 const char *Yvalues_before,
 const char *Xvalues_after,
 const char *Yvalues_after,
 ShuffleValidityProof shuffle_validity_proof,
 CheckResults *check_shuffle_answer_result)
{
   // Assume success until told otherwise
   int result = 0;
   // A counter used for loops
   int icount = 0;
   *check_shuffle_answer_result = NULL;
   // An OpenSSL structure that holds BIGNUM temporary variables
   // used by library functions
   auto_BN_CTX ctx(BN_CTX_new());

   try
   {  // Get values out of xml and build simple structure to pass to
      // hashing function
      // An xml tree from the shuffle_validity_proof input
      VHUtil::xml_tree xml_svp(shuffle_validity_proof);
      // The root node of xml_svp
      VHUtil::xml_node root_svp = xml_svp.root();
      // The node containing the SimpleShuffleValidityProof
      VHUtil::xml_node node_ssvp = root_svp->e(SIMPLE_SHUFFLE_VALIDITY_PROOF);
      
      // An empty xml tree to hold inputs to a hash
      VHUtil::xml_tree xml_hash_inputs("<HashInputs/>");
      // The root node of xml_hash_inputs
      VHUtil::xml_node root_hash_inputs = xml_hash_inputs.root();
      root_hash_inputs->add_element(root_svp->e(U_VALUES)->deep_copy());
      root_hash_inputs->add_element(root_svp->e(W_VALUES)->deep_copy());
      root_hash_inputs->add_element(root_svp->e(A_VALUES)->deep_copy());
      root_hash_inputs->add_element(root_svp->e(C_VALUES)->deep_copy());
      root_hash_inputs->add_element(root_svp->e(LAMBDA_1)->deep_copy());
      root_hash_inputs->add_element(root_svp->e(LAMBDA_2)->deep_copy());
      root_hash_inputs->add_element(node_ssvp->e(G_VALUE)->deep_copy());
      root_hash_inputs->add_element(node_ssvp->e(BIG_GAMMA)->deep_copy());
      // A stream to hold xml_hash_inputs
      std::ostringstream oss_hash_input;
      oss_hash_input << xml_hash_inputs;
      
      // Generate rho[i=1 to k] and lambda
      // The return value from generate_shuffle_hash_values
      auto_freeing< ConstCharStar > rho_values = 0;
      VH_propagate(generate_shuffle_hash_values
                   (xml_bb,
                    Xvalues_before, Yvalues_before, oss_hash_input.str().c_str(),
                    Xvalues_after, Yvalues_after, &rho_values), "GEN_SHUF_HASHVAL");
      
      // Calculate Rs and Ss
      // The RValues that are returned from generate_simple_check_inputs
      auto_freeing< ConstCharStar > RValues = 0;
      // The SValues that are returned from generate_simple_check_inputs
      auto_freeing< ConstCharStar > SValues = 0;
      VH_propagate(generate_simple_check_inputs
                   (xml_bb,
                    shuffle_validity_proof, rho_values, &RValues, &SValues),
         "GEN_SIMPLE_CHK_INPUTS");
      
      // Get simple_shuffle_validity_proof out of shuffle_validity_proof;
      // A stream to hold node_ssvp
      std::ostringstream ssvp_stream;
      ssvp_stream << *node_ssvp;
      
      // Call check_simple_shuffle here
      // The return value from check_simple_k_shuffle_long
      auto_freeing<CheckResults> check_simple_shuffle_result_long = 0;
      VH_propagate(check_simple_k_shuffle_long
                   (xml_bb,
                    RValues, SValues,
                    ssvp_stream.str().c_str(),
                    &check_simple_shuffle_result_long), "CHK_SIMPLE_SHUFFLE");
      
      // Check Phi values
      // The return value of check_values
      auto_freeing< CheckResults > check_values_result = 0;
      VH_propagate(check_values(xml_bb, Xvalues_before,
         Yvalues_before, Xvalues_after, Yvalues_after, rho_values,
         shuffle_validity_proof, &check_values_result), "CHK_VALUES");
      
      *check_shuffle_answer_result = VHTI_dup(check_values_result);
   }
   catch (const VHUtil::Exception & e)
   {
      VHTI_set_last_error(e);
      result = e.getResultNo();
   }
   
   return result;
}

int
VHInternal::check_simple_k_shuffle_long
(VHUtil::xml_tree &xml_bb,
 const char *Xvalues,
 const char *Yvalues,
 SimpleShuffleValidityProof simple_shuffle_validity_proof,
 CheckResults *check_simple_shuffle_result)
{
   // Assume success until told otherwise
   int result = 0;
   *check_simple_shuffle_result = NULL;
   // A counter used for loops
   int icount = 0;
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
   
   try
   {
      // Get p, q, and g out of CryptoElectionParameters in SignedBlank Ballot
      VHInternal::get_election_parameters(xml_bb, pm,
         qm, gen, ePublicKey);
      
      // Get X and Y values out of XML, put into vector
      // A vector of auto_BN to hold the X values
      std::vector< auto_BN > X_vec;
      // A vector of auto_BN to hold the Y values
      std::vector< auto_BN > Y_vec;
      // An xml tree from the Xvalues input
      VHUtil::xml_tree xml_Xvalues(Xvalues);
      // The root node of xml_Xvalues
      VHUtil::xml_node root_Xvalues = xml_Xvalues.root();
      // An xml tree from the Yvalues input
      VHUtil::xml_tree xml_Yvalues(Yvalues);
      // The root node of xml_Yvalues
      VHUtil::xml_node root_Yvalues = xml_Yvalues.root();
      
      // Number of ballots (could have been determined from other data as well)
      int ksize = root_Xvalues->element_count();
      for (icount=0; icount<ksize; icount++)
      {
         X_vec.push_back(xml2BN(root_Xvalues->e(icount)));
         Y_vec.push_back(xml2BN(root_Yvalues->e(icount)));
      }
      
      // Get everything out of the simple_shuffle_validity_proof
      // A string from the simple_shuffle_validity_proof input
      std::string svp_str(simple_shuffle_validity_proof);
      // An xml tree from svp_str
      VHUtil::xml_tree xml_svp(svp_str);
      // The root node of xml_svp
      VHUtil::xml_node root_svp = xml_svp.root();
      // The value of G, a generator of gen
      auto_BN GValue = xml2BN(root_svp->e(G_VALUE));
      // The value of G^gamma
      auto_BN BigGamma = xml2BN(root_svp->e(BIG_GAMMA));
      
      // Get alpha values out of xml
      // A vector of auto_BN to hold the alpha values
      std::vector< auto_BN > alpha_vec;
      // The node containing the alpha values
      VHUtil::xml_node alphas_node = root_svp->e(ALPHA_VALUES);
      // The number of alpha values
      int num_alphas = alphas_node->element_count();
      for (icount = 0; icount<num_alphas; icount++)
      {
         alpha_vec.push_back(xml2BN(alphas_node->e(icount)));
      }

      // Get Theta values out of xml
      // A vectore of auto_BN to hold the Theta values
      std::vector< auto_BN > Theta_vec;
      // The node containing the Theta values
      VHUtil::xml_node Thetas_node = root_svp->e(THETA_VALUES);
      // The number of Theta values
      int num_Thetas = Thetas_node->element_count();
      for (icount = 0; icount<num_Thetas; icount++)
      {
         Theta_vec.push_back(xml2BN(Thetas_node->e(icount)));
      }
      
      // Calculate t_hash
      // t = Hash( G_value, BigGamma, {X_i}, {Y_i} )
      // An array of BIGNUM to hold values for hashing
      VHUtil::array< const BIGNUM * > arr1( 2 + 2*ksize );
      arr1[0] = GValue;
      arr1[1] = BigGamma;
      
      // Now append the other items
      // The index of the array items
      int arr_index1 = 2;
      for (icount=0; icount<ksize; icount++)
      {
         arr1[arr_index1] = X_vec[icount];
         arr_index1++;
      }
      for (icount=0; icount<ksize; icount++)
      {
         arr1[arr_index1] = Y_vec[icount];
         arr_index1++;
      }
      
      // The hash values of all of the array items
      auto_BN t_hash = GetHashOfNBNs(arr1, arr1.m_size);
      t_hash.Canonicalize(qm);
      
      // Calculate multipliers:  U = GValue^-t, W = BigGamma^-t
      // Raising to the -t is the same as raising to the q-t
      // An auto_BN to hold q-t
      auto_BN q_minus_t;
      VH_nonzero(BN_sub(q_minus_t, qm, t_hash), BN_SUB);
      q_minus_t.Canonicalize(qm);
      
      // An auto_B to hold the U value
      auto_BN U_value;
      VHInternal::fixed_mod_exp(U_value, GValue, q_minus_t,
                                pm, ctx);
      
      // An auto_BN to hold the W value
      auto_BN W_value;
      VHInternal::fixed_mod_exp(W_value, BigGamma, q_minus_t,
                                pm, ctx);
      
      // Calculate big Xbars
      // A vector of auto_BN to hold the Xbar values
      std::vector< auto_BN > Xbar_vec;
      for (icount=0; icount<ksize; icount++)
      {
         // An auto_BN to hold the current Xbar value
         auto_BN Xbar;
         BN_mod_mul(Xbar, X_vec[icount], U_value, pm, ctx);
         Xbar_vec.push_back(Xbar);
      }
      
      // Calculate big Ybars
      // A vector of auto_BN to hold the Ybar values
      std::vector< auto_BN > Ybar_vec;
      for (icount=0; icount<ksize; icount++)
      {
         // An auto_BN to hold the current Ybar value
         auto_BN Ybar;
         VH_nonzero(BN_mod_mul(Ybar, Y_vec[icount], W_value, pm, ctx), BN_MOD_MUL);
         Ybar_vec.push_back(Ybar);
      }

      // Now generate c
      // c_hash = H(G_value, BigGamma, {X}, {Y}, {Theta});
      // An array of BIGNUM to hold values for hashing
      VHUtil::array< const BIGNUM * > arr2( 2 + ksize + ksize + 2*ksize);
      for (icount=0; icount<arr1.m_size; icount++)
      {
         arr2[icount] = arr1[icount];
      }
      
      // Now append the Theta values
      // The index of the array items
      int arr_index2 = arr1.m_size;
      for (icount=0; icount<2*ksize; icount++)
      {
         arr2[arr_index2] = Theta_vec[icount];
         arr_index2++;
      }
      // The value of the hash of the array items
      auto_BN c_hash = GetHashOfNBNs(arr2, arr2.m_size);
      c_hash.Canonicalize(qm);
      
      // Now generate {check_Theta}  -- formerly known as {A}
      // A vector of auto_BN to hold the check_Theta values
      std::vector< auto_BN > check_Theta_vec;
      for (icount=0; icount<ksize; icount++)
      {
         // An auto_BN to hold Xbar^c_hash
         auto_BN tmp1;
         // An auto_BN to hold Ybar^(-alpha)
         auto_BN tmp2;
         
         // An auto_BN for -alpha = q-alpha
         auto_BN minus_alpha;
         VH_nonzero(BN_sub(minus_alpha, qm, alpha_vec[icount]), BN_SUB);
         minus_alpha.Canonicalize(qm);
         
         if (icount == 0)
         {
            VH_nonzero(BN_mod_exp(tmp1, Xbar_vec[icount], c_hash, pm, ctx), BN_MOD_EXP);
            VH_nonzero(BN_mod_exp(tmp2, Ybar_vec[icount], minus_alpha, pm, ctx), BN_MOD_EXP);
         }
         else
         {
            VH_nonzero(BN_mod_exp(tmp1, Xbar_vec[icount], alpha_vec[icount-1], pm, ctx), BN_MOD_EXP);
            VH_nonzero(BN_mod_exp(tmp2, Ybar_vec[icount], minus_alpha, pm, ctx), BN_MOD_EXP);
         }

         // An auto_BN to hold the current check_Theta_value
         auto_BN check_Theta_value;
         VH_nonzero(BN_mod_mul(check_Theta_value, tmp1, tmp2, pm, ctx), BN_MOD_MUL);
         check_Theta_vec.push_back(check_Theta_value);
      }
      for (icount=ksize; icount<2*ksize; icount++)
      {
         // An auto_BN to hold BigGamma^alpha
         auto_BN Gamma_term;
         // An auto_BN to hold G^(-c_hash)
         auto_BN G_term;
         // An auto_BN to hold the check_Theta_value
         auto_BN check_Theta_value;

         VHInternal::fixed_mod_exp(Gamma_term, BigGamma,
                                   alpha_vec[icount-1], pm, ctx);
         if (icount == (2*ksize - 1) )
         {
            // An auto_BN to hold -c_hash = q-c_hash
            auto_BN minus_c_hash;
            VH_nonzero(BN_sub(minus_c_hash, qm, c_hash), BN_SUB);
            minus_c_hash.Canonicalize(qm);
            VHInternal::fixed_mod_exp(G_term, GValue, minus_c_hash,
                                      pm, ctx);
         }
         else
         {
            // An auto_BN to hold -alpha = q-alpha
            auto_BN minus_alpha;
            VH_nonzero(BN_sub(minus_alpha, qm, alpha_vec[icount]), BN_SUB);
            minus_alpha.Canonicalize(qm);
            VHInternal::fixed_mod_exp(G_term, GValue, minus_alpha,
                                      pm, ctx);
         }

         VH_nonzero(BN_mod_mul(check_Theta_value, Gamma_term, G_term, pm, ctx), BN_MOD_MUL);
         check_Theta_vec.push_back(check_Theta_value);
      }
      
      // Now check the Thetas against the check_Thetas
      for (icount=0; icount<Theta_vec.size(); icount++)
      {
         result = BN_cmp(Theta_vec[icount], check_Theta_vec[icount]);
         if (result != 0)
         {
            break;
         }
      }
      
      // An empty xml tree to hold the CheckResults
      VHUtil::xml_tree xml_vr("<" CHECK_RESULTS "/>");
      // The root node of xml_vr
      VHUtil::xml_node root_vr = xml_vr.root();
      
      if (result != 0)
      {
         VHUtil::cout() << "Check Simple Shuffle Failed" << std::endl;
         root_vr->add_characters("Simple Check Failure");
      }
      else
      {
         root_vr->add_characters("Simple Check Success");
      }
      
      // A stream to hold xml_vr
      std::ostringstream vr_stream;
      vr_stream << xml_vr;
      *check_simple_shuffle_result = VHTI_dup(vr_stream.str().c_str());
   }
   catch (const VHUtil::Exception & e)
   {
      VHTI_set_last_error(e);
      result = e.getResultNo();
   }
   return result;
}
