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
#include <util/sslerror.h>
#include <string>
#include <sstream>
#include <set>

std::vector< int >
VHInternal::get_permutation_vector_from_xml(Permutation permutation)
{
   // A string holding the permutation values
   std::istringstream perm_str (VHUtil::xml_tree (permutation).root ()->characters());
   // A vector to hold the permutation elements
   std::vector< int > perm_vec;
   
   // Put the permutation values into a vector

   do
   {
      int tmp;
      perm_str >> tmp;
      if (perm_str) 
         perm_vec.push_back(tmp);
   } while (perm_str);

   return perm_vec;
}

void
VHInternal::combine_pre_vv_results
(PreVerificationCodeBoxes all_trustee_pre_vcodes,
 VHUtil::xml_tree &blank_ballot,
 RawBallotBox * verification_raw_ballot_box)
{
   * verification_raw_ballot_box = 0;
   auto_BN pm(NULL); // The Election Modulus
   auto_BN qm(NULL); // The Election Subgroup Modulus
   auto_BN gen(NULL); // The Election Subgroup Generator
   auto_BN ePublicKey(NULL); // The Election Public Key
   // An OpenSSL structure that holds BIGNUM temporary variables
   // used by library functions
   auto_BN_CTX ctx(BN_CTX_new());
   if (!ctx)
      throw SSL_ERROR;

   // Here's where we multiply all of the Xs and Ys together to get the
   // CheckXs and CheckYs.  The output will look like a single copy of
   // a Raw Ballot Box

   VH_zero (::VHTI_validate(PRE_VERIFICATION_CODE_BOXES,
                            all_trustee_pre_vcodes),
            VALIDATION_FAILURE) ;

   VHInternal::get_election_parameters (blank_ballot, pm,
                                        qm, gen, ePublicKey);
   int num_questions = 0; // Find out how many questions

   for (int elem_bb=0; elem_bb < blank_ballot.root ()->element_count(); elem_bb++)
   {
      if (blank_ballot.root ()->e(elem_bb)->name() == BALLOT_QUESTION) {
         num_questions++;
      }
   }

   // An xml tree from the all_trustee_pre_vcodes input
   VHUtil::xml_tree xml_all_pvcs(all_trustee_pre_vcodes);
   // The root node of xml_all_pvcs
   VHUtil::xml_node root_all_pvcs = xml_all_pvcs.root();
   // The node containing the first PreVerificationCodeBox
   VHUtil::xml_node first_pvc_box =
      root_all_pvcs->e(PRE_VERIFICATION_CODE_BOX);
   // The node containing the first RawBallotBox
   VHUtil::xml_node first_rbb = first_pvc_box->e(RAW_BALLOT_BOX);
   // How many ballots per box
   int num_ballots_per_box = first_rbb->element_count();

   // Make empty RawBallotBox for return
   VHUtil::xml_tree xml_return_rbb("<" RAW_BALLOT_BOX "/>");
   // The root node of xml_return_rbb
   VHUtil::xml_node root_return_rbb = xml_return_rbb.root();

   for (int nbal=0; nbal<num_ballots_per_box; nbal++)
   {  // A node for a RawVotedBallot
      VHUtil::xml_node root_rvb =
         root_return_rbb->new_element(RAW_VOTED_BALLOT);
      for (int nq=0; nq<num_questions; nq++)
      {
         std::vector< auto_BN > Xvec; // A vector to hold th X values
         std::vector< auto_BN > Yvec; // A vector to hold the Y values
         for (int num_bbox=0; // How many trustees
         num_bbox < root_all_pvcs->element_count(); num_bbox++)
         {
            // The current ballot box
            VHUtil::xml_node current_bbox =
               root_all_pvcs->e(num_bbox); // Which trustee's PCCs
            // The RawBallotBox in the current ballot box
            VHUtil::xml_node current_rbb =current_bbox->e(RAW_BALLOT_BOX);
            // The current RawVotedBallot
            VHUtil::xml_node current_rvb = current_rbb->e(nbal);
            // The current question
            VHUtil::xml_node current_question = current_rvb->e(nq);
            // The X value of the current ElGamal Pair
            auto_BN Xval = xml2BN(current_question->e(X_VALUE));
            // The Y value of the current ElGamal Pair
            auto_BN Yval = xml2BN(current_question->e(Y_VALUE));
            Xvec.push_back(Xval);
            Yvec.push_back(Yval);
         }
         // Once you have all of the Xs and Ys for one question
         // for one ballot, multiply them all together
         // A node for the ElGamal new Pair
         VHUtil::xml_node root_egp = root_rvb->new_element(EL_GAMAL_PAIR);

         auto_BN current_x_prod; // The current X product
         VH_nonzero(BN_one(current_x_prod), BN_ONE);
         auto_BN current_y_prod; // The current Y product
         VH_nonzero(BN_one(current_y_prod), BN_ONE);
         for (int num_pairs=0; num_pairs<Xvec.size(); num_pairs++)
         {
            if (!BN_mod_mul(current_x_prod, current_x_prod,
               Xvec[num_pairs], pm, ctx))
               throw SSL_ERROR;

            if (!BN_mod_mul(current_y_prod, current_y_prod,
               Yvec[num_pairs], pm, ctx))
               throw SSL_ERROR;
         }
         add_BN_element(root_egp, X_VALUE, current_x_prod, DEC);
         add_BN_element(root_egp, Y_VALUE, current_y_prod, DEC);
      }
   }
   std::ostringstream oss; // A stream to hold xml_return_rbb
   oss << xml_return_rbb;
   *verification_raw_ballot_box = VHTI_dup(oss.str().c_str());

}

namespace {
void
assemble_raw_cleartext_ballots(auto_BN_CTX &ctx,
               const auto_BN &pm,
               const int num_rvb,
               const int num_auth_pd,
               VHUtil::xml_node &root_ctbs,
               VHUtil::xml_node &node_rbb,
               VHUtil::xml_node &node_auth_pds,
               std::vector< auto_BN > &lambda_values,
               std::string &result_text)
{
   // A vector to hold the ElGamal pair Y values
   std::vector< auto_BN > egp_y_values;

   // Vectors to hold various phases of the decrypt
   std::vector< auto_BN > pre_answers;
   std::vector< auto_BN > copy;
   std::vector< auto_BN > pre_final;
   std::vector< auto_BN > final;
               
   // For each RawVotedBallot
   for (int nrvb=0; nrvb<num_rvb; nrvb++)
   {
      // The root node of xml_ctb
      VHUtil::xml_node root_ctb =
         root_ctbs->new_element(RAW_CLEAR_TEXT_BALLOT);
      // The node containing the RawVotedBallot
      VHUtil::xml_node rvb_node = node_rbb->e(nrvb);
                  
      // Now get out XValues and YValues
      // clear out values
      egp_y_values.clear();
      pre_answers.clear();
      // How many AuthorityPartialDecrypt objects
      for (int j=0; j<num_auth_pd; j++)
      {  // AuthorityPartialDecrypts
         VHUtil::xml_node apd_node = node_auth_pds->e(j);
         // BallotBoxPartialDecrypt
         VHUtil::xml_node bbpd_node =
            apd_node->e(BALLOT_BOX_PARTIAL_DECRYPT);
         VHUtil::xml_node bpd_node =
            bbpd_node->e(nrvb);  // BallotPartialDecrypt
         // The number of answers
         int num_answers = bpd_node->element_count();
         // lambda for one authority at a time
         auto_BN current_lambda = lambda_values[j];
         pre_answers.clear();
         for (int egp_count=0; egp_count<num_answers; egp_count++)
         {
            // The current AnswerPartialDecrypt
            VHUtil::xml_node apd_node =
               bpd_node->e(ANSWER_PARTIAL_DECRYPT, egp_count);
            auto_BN x_value =
               xml2BN(apd_node->e(X_VALUE));  // decryption share
            if (j == 0)
            {
               // Same for all authorities so only get them once
               auto_BN y_value =
                  xml2BN(rvb_node->e(EL_GAMAL_PAIR,
                                     egp_count)->e(Y_VALUE));
               egp_y_values.push_back(y_value);  
            }
                        
            // Calculate (decryption share)^lambda
            auto_BN ds_raise_lambda;
            if (!BN_mod_exp(ds_raise_lambda, x_value,
                            current_lambda, pm, ctx))
               throw SSL_ERROR;
            pre_answers.push_back(ds_raise_lambda);
         }
                     
         // After you going through the ballot for this authority,
         // multiply answer elements in the vector by ones from
         // the other authorities
         if (j == 0)  
         {
            // Nothing to multiply, just save answer data in a copy
            copy.clear();
            for (int sv=0; sv<pre_answers.size(); sv++)
            {
               copy.push_back(pre_answers[sv]);
            }
         }
         else
         {
            // pre_answer * copy
            auto_BN tmp_numerator;
            pre_final.clear();
            for (int s1=0; s1<pre_answers.size(); s1++)
            {
               if (!BN_mod_mul(tmp_numerator, pre_answers[s1],
                               copy[s1], pm, ctx))
                  throw SSL_ERROR;
               pre_final.push_back(tmp_numerator);
            }
            copy.clear();
            for (int s2=0; s2<pre_final.size(); s2++)
            {
               copy.push_back(pre_final[s2]);
            }
         }   
      }
                  
      // Divide Y-Value by combined decrypted X-Value
      // to get final decryption.
      if (egp_y_values.size() != copy.size())
      {
         std::ostringstream whine;
         whine << "In ballot " << nrvb << " of " << num_rvb
               << ": failure in partial decrypt combine:"
               << " number of Y values differs from `copy'";
         result_text = whine.str();
      }
      else
      {
         // Check is complete; now create the clear-text ballots.

         final.clear();
         for (int val_size=0;
              val_size<egp_y_values.size(); val_size++)
         {
            auto_BN decrypt_value; // The decrypt value
            // The inverse of the denominator
            auto_BN inv_denom;
            auto_BN denom = copy[val_size]; // The denominator
            // The numerator
            auto_BN num = egp_y_values[val_size];
            if (!BN_mod_inverse(inv_denom, denom, pm, ctx))
               throw SSL_ERROR;
            if (!BN_mod_mul(decrypt_value, num, inv_denom, pm, ctx))
               throw SSL_ERROR;
            final.push_back(decrypt_value);
         }
                     
         for (int num_marks=0; num_marks<final.size(); num_marks++)
         {
            // Add AnswerMark to the RawClearTextBallot structure
            add_BN_element(root_ctb,ANSWER_MARK, final[num_marks]);
         }
      }
   }// for nrvb
}
}

void
VHInternal::check_partial_decrypts_and_combine
(SignedBlankBallot signed_blank_ballot,
 GeneralPurposePublicKey ballot_signing_key,
 PartiallyDecryptedBallotBox pd_ballot_box,
 RawClearTextBallots *raw_clear_text_ballots,
 CheckResults *combine_partial_decrypt_result)
{
   int retval = 0; // return values from BN functions
   *raw_clear_text_ballots = NULL;
   *combine_partial_decrypt_result = NULL;
   // A vector to hold the authority evaluation points
   std::vector< auto_BN > auth_eval_points;
   // A vector to hold the key share commitment values
   std::vector< auto_BN > ksc_values;
   // A vector to hold the lambda values
   std::vector< auto_BN > lambda_values;
   auto_BN pm(NULL); // The Election Modulus
   auto_BN qm(NULL); // The Election Subgroup Modulus
   auto_BN gen(NULL); // The Election Subgroup Generator
   auto_BN ePublicKey(NULL); // The Election Public Key
   // An OpenSSL structure that holds BIGNUM temporary variables
   // used by library functions
   auto_BN_CTX ctx(BN_CTX_new());
   if (!ctx) throw SSL_ERROR;

   // This is the text of the result that we'll return.  If it's still
   // empty by the time we get to the end of this function (and if
   // result is 0), that means that everything checked OK.
   std::string result_text;
   
   VHUtil::safe_xml_tree xml_bb (signed_blank_ballot, BLANK_BALLOT, ballot_signing_key);

   VHUtil::xml_tree xml_ctbs("<" RAW_CLEAR_TEXT_BALLOTS "/>");
   // The root node of xml_ctbs
   VHUtil::xml_node root_ctbs = xml_ctbs.root();
      
   // Get RawBallotBox out of PartiallyDecryptedBallotBox
   VHUtil::xml_tree xml_pdbb(pd_ballot_box);
   // The root node of xml_pdbb
   VHUtil::xml_node root_pdbb = xml_pdbb.root();
   // The node containing the RawBallotBox
   VHUtil::xml_node node_rbb = root_pdbb->e(RAW_BALLOT_BOX);

   // The node containing the AuthorityPartialDecrypts
   VHUtil::xml_node node_auth_pds = root_pdbb->e(AUTHORITY_PARTIAL_DECRYPTS);
   // The number of AuthorityPartialDecrypt objects
   int num_auth_pd = node_auth_pds->element_count();
      
   // Now check each partial decrypt before proceeding with combine
   for (int npd=0; npd<num_auth_pd; npd++)
   {
      // The current AuthorityPartialDecrypt
      VHUtil::xml_node node_auth_pd =
         node_auth_pds->e(AUTHORITY_PARTIAL_DECRYPT, npd);
      std::ostringstream stream_apd; // A stream to hold node_auth_pd
      stream_apd << *node_auth_pd;
         
      // The returning result
      auto_freeing<CheckResults> check_partial_decrypt_result = 0;
      VH_propagate (VHTI_check_partial_decrypt
                    (node_rbb->str().c_str(),
                     stream_apd.str().c_str(), signed_blank_ballot,
                     ballot_signing_key,
                     &check_partial_decrypt_result), "VRPRDCMB");

      if (!strstr (check_partial_decrypt_result, CHECK_SUCCESS_TEXT))
      {
         VHUtil::cout() << " failed ("
                        << (const char *)check_partial_decrypt_result << ")."
                        << std::endl;
         *combine_partial_decrypt_result =
            VHTI_dup(check_partial_decrypt_result);
         break;
      }
   }
      
   if (!*combine_partial_decrypt_result)
   {
      // First find out how many Ballots are in a BallotBox
      // The first AuthorityPartialDecrypt in the batch
      VHUtil::xml_node first_auth_pd =
         node_auth_pds->e(AUTHORITY_PARTIAL_DECRYPT);
      // The first BallotBoxPartialDecrypt
      VHUtil::xml_node first_bbpd_node =
         first_auth_pd->e(BALLOT_BOX_PARTIAL_DECRYPT);
      // The number of ballots in a BallotBox
      int num_bpd = first_bbpd_node->element_count();
         
      // Make sure it's the same number as in the RawBallotBox
      int num_rvb = node_rbb->element_count();
      VH_nonzero (num_bpd == num_rvb, "NUMPD_NE_NUMRVB");
         
      // Get ElectionModulus (p) and ElectionSubgroupModulus (q)
      // out of CryptoElectionParameters in the SignedBlank Ballot
      // Get ElectionPublicKey (h) out of CryptoTabulationParameters
      VHInternal::get_election_parameters(xml_bb,
                                          pm, qm, gen, ePublicKey);
         
      // Each AuthorityPartialDecrypt has the committed authority object
      // who did the partial decrypts on that RBB
      for (int i=0; i<num_auth_pd; i++)
      {
         // Get all authority evaluation points and KeyShareCommitment values
         // The current AuthorityPartialDecrypt node
         VHUtil::xml_node auth_pd_node = node_auth_pds->e(i);
         // The Authority node
         VHUtil::xml_node auth_node =
            auth_pd_node->e(COMMITTED_AUTHORITY)->e(AUTHORITY);
         // The value of the AuthorityEvaluationPoint
         auto_BN aep = xml2BN(auth_node->e(AUTHORITY_EVALUATION_POINT));
         auth_eval_points.push_back(aep);
         // The value of the KeyShareCommitment
         auto_BN ksc = xml2BN(auth_pd_node->
                              e(COMMITTED_AUTHORITY)->e(KEY_SHARE_COMMITMENT));
         ksc_values.push_back(ksc);
      }
         
      // Now that you have all of the authorities,
      // calculate the lambdas using Lagrange's Theorem
      for (int na=0; na<auth_eval_points.size(); na++)
      {
         auto_BN num; // The numerator
         if (!BN_one (num))
            throw SSL_ERROR;
         auto_BN denom; // The denominator
         if (!BN_one (denom))
            throw SSL_ERROR;
         auto_BN zero_bn; // An auto_BN with the value of zero
         if (!BN_zero(zero_bn))
            throw SSL_ERROR;
            
         // Hold one authority constant while cycling through the others
         // current_auth could also be referred to a Z_sub_i
         // The evaluation point of the current authority
         auto_BN current_auth = auth_eval_points[na];
         for (int other_na=0; other_na<auth_eval_points.size(); other_na++)
         {
            if (na != other_na)  // Skip the current authority
            {
               auto_BN minus_Z_sub_j; // -Z_j
               VH_nonzero (BN_sub(minus_Z_sub_j, zero_bn,
                                  auth_eval_points[other_na]), "VPDCSUB1");
               minus_Z_sub_j.Canonicalize(qm);
               // The temporary value of the denominator
               auto_BN denom_tmp;
               VH_nonzero (BN_sub(denom_tmp, current_auth,
                                  auth_eval_points[other_na]), "VPDCSUB2");
               denom_tmp.Canonicalize(qm);
                  
               VH_nonzero (BN_mod_mul (num, num, minus_Z_sub_j, qm, ctx),
                           "VPDCMUL1");
               VH_nonzero (BN_mod_mul (denom, denom, denom_tmp, qm, ctx),
                           "VPDCMUL2");
            }
         }
         // Divide the numerator by the denominator, and that is lambda
         auto_BN lambda;
         auto_BN inv_denom;
            
         // NOTE: We should decide which is better:
         // using the BN_mod_inverse function
         // or raising the denominator to the -1 power
         VH_nonzero (BN_mod_inverse(inv_denom, denom, qm, ctx), "VPDCINV1");
         VH_nonzero (BN_mod_mul(lambda, num, inv_denom, qm, ctx),"VPDCMUL3");
         lambda_values.push_back(lambda);
      }
         
      // Now that you have the KeyShareCommitment and lambda values for each
      // authority, check them against the ElectionPublicKey
      // h = SUM(ksc^lambda)
      if (ksc_values.size() != lambda_values.size())
      {
         result_text = "Failure in partial decrypt combine:"
            " not the same number of ksc and lambda values";
      }
      else
      {
         auto_BN running_product; // The running product
         if (!BN_one (running_product))
            throw SSL_ERROR;
         for (int i=0; i<ksc_values.size(); i++)
         {
            auto_BN k_val = ksc_values[i]; // Current key share commitment
            auto_BN l_val = lambda_values[i]; // The current lambda value
            auto_BN exp_val;
            VH_nonzero (BN_mod_exp(exp_val, k_val, l_val, pm, ctx),
                        "VPDCEXP1");
            VH_nonzero (BN_mod_mul(running_product, running_product,
                                   exp_val, pm, ctx), "VPDCMUL4");
         }
            
         // Now compare it with the ElectionPublicKey from SignedBlankBallot
         if (BN_cmp(ePublicKey, running_product))
         {
            std::ostringstream whine;
            whine << "Failure in partial decrypt combine: ePublicKey "
                  << ePublicKey
                  << " differs from running product "
                  << running_product;
            result_text = whine.str();
         }
         else
         {
            assemble_raw_cleartext_ballots(ctx,
                                           pm,
                                           num_rvb,
                                           num_auth_pd,
                                           root_ctbs,
                                           node_rbb,
                                           node_auth_pds,
                                           lambda_values,
                                           result_text);
         }
      }

      if (0 == result_text.size())
         result_text = CHECK_SUCCESS_TEXT;

      // An empty xml tree to hold CheckResults
      VHUtil::xml_tree xml_res("<" CHECK_RESULTS "/>");
      xml_res.root ()->add_characters (result_text);

      * combine_partial_decrypt_result = VHTI_dup(xml_res.str().c_str());
      std::ostringstream ctbs_stream; // A stream to hold xml_ctbs
      ctbs_stream << xml_ctbs;
      *raw_clear_text_ballots = VHTI_dup(ctbs_stream.str().c_str());
   }
}

void
VHInternal::generate_el_gamal_sequences(VHUtil::xml_tree &xml_bb,
                                        const char * X_values,
                                        const char * Y_values,
                                        const char * X_values_out,
                                        const char * Y_values_out,
                                        const char **X_hats,
                                        const char **Y_hats,
                                        const char **X_checks,
                                        const char **Y_checks,
                                        const char **e_values)
{
   *X_hats = NULL;
   *Y_hats = NULL;
   *X_checks = NULL;
   *Y_checks = NULL;
   *e_values = NULL;
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
   if (!ctx)
      throw SSL_ERROR;

   VHInternal::get_election_parameters (xml_bb, pm,
                                        qm, gen, ePublicKey);
   VHUtil::xml_node root_bb = xml_bb.root();

   // An xml tree from the X_values input
   VHUtil::xml_tree xml_Xvalues(X_values);
   // The root node of xml_Xvalues
   VHUtil::xml_node root_Xvalues = xml_Xvalues.root();
   // An xml tree from the Y_values input
   VHUtil::xml_tree xml_Yvalues(Y_values);
   // The root node of xml_Yvalues
   VHUtil::xml_node root_Yvalues = xml_Yvalues.root();
   // The number of ballots
   int ksize = root_Xvalues->element_count();

   // An xml tree from the X_values_out input
   VHUtil::xml_tree xml_Xvalues_out(X_values_out);
   // The root node of xml_Xvalues_out
   VHUtil::xml_node root_Xvalues_out = xml_Xvalues_out.root();
   // An xml tree from the Y_values_out input
   VHUtil::xml_tree xml_Yvalues_out(Y_values_out);
   // The root node of xml_Yvalues_out
   VHUtil::xml_node root_Yvalues_out = xml_Yvalues_out.root();

   // An empty xml tree for the product of each ballot's X values
   VHUtil::xml_tree xml_Xhats("<Xhats/>");
   // The root node of xml_Xhats
   VHUtil::xml_node root_Xhats = xml_Xhats.root();
   // An empty xml tree for the product of each ballot's Y values
   VHUtil::xml_tree xml_Yhats("<Yhats/>");
   // The root node of xml_Yhats
   VHUtil::xml_node root_Yhats = xml_Yhats.root();
   // An empty xml tree for the product of each ballot's X_out values
   VHUtil::xml_tree xml_Xchecks("<Xchecks/>");
   // The root node of xml_Xchecks
   VHUtil::xml_node root_Xchecks = xml_Xchecks.root();
   // An empty xml tree for the product of each ballot's Y_out values
   VHUtil::xml_tree xml_Ychecks("<Ychecks/>");
   // The root node of xml_Ychecks
   VHUtil::xml_node root_Ychecks = xml_Ychecks.root();

   int num_questions = 0; // How many questions in a ballot
   int num_elems_bb = root_bb->element_count();
   for (int i_bb=0; i_bb<num_elems_bb; i_bb++)
   {
      if (root_bb->e(i_bb)->name() == BALLOT_QUESTION)
      {
         num_questions++;
      }
   }

   // Generate e values from a hash of the inputs and outputs
   // An array to hold the items to hash
   VHUtil::array< const BIGNUM * > arr( 4*num_questions*ksize );
   int index=0;
   for (icount=0; icount<ksize; icount++)
   {
      // The X values for the current ballot
      VHUtil::xml_node current_X_ballot = root_Xvalues->e(BALLOT, icount);
      // The Xbar values for the current ballot
      VHUtil::xml_node current_Xbar_ballot =
         root_Xvalues_out->e(BALLOT, icount);
      // The Y values for the current ballot
      VHUtil::xml_node current_Y_ballot = root_Yvalues->e(BALLOT, icount);
      // The Ybar values for the current ballot
      VHUtil::xml_node current_Ybar_ballot =
         root_Yvalues_out->e(BALLOT, icount);
      for (int jcount=0; jcount<num_questions; jcount++)
      {
         arr[index] = xml2BN(current_X_ballot->e(X_VALUE, jcount));
         index++;
         arr[index] = xml2BN(current_Xbar_ballot->e(X_VALUE, jcount));
         index++;
         arr[index] = xml2BN(current_Y_ballot->e(Y_VALUE, jcount));
         index++;
         arr[index] = xml2BN(current_Ybar_ballot->e(Y_VALUE, jcount));
         index++;
      }
   }

   // The hash of all the array elements
   auto_BN e_hash_val = GetHashOfNBNs(arr, arr.m_size);
   // Character representation of the hash value
   const char * ch_e_hash_val = BN_bn2dec(e_hash_val);
   // xml to hold the RandoSeedKey
   std::string key_str("<" RANDOM_SEED_KEY ">");
   key_str += ch_e_hash_val;
   key_str += "</" RANDOM_SEED_KEY ">";
      
   // The random state generated
   auto_freeing<RandomState> random_state = 0;
   VH_propagate(VHTI_generate_random_state(key_str.c_str(), &random_state),
                GENERATE_RANDOM_STATE);
   // A RandomState object
   VHInternal::RS rs (static_cast<RandomState>(random_state));
   // A vector to hold the random e values
   std::vector< auto_BN > e_vec;
   // An empty xml tree to hold the e values
   VHUtil::xml_tree xml_e_values("<e_values/>");
   // The root node of xml_e_values
   VHUtil::xml_node root_e_values = xml_e_values.root();
   for (icount=0; icount<num_questions; icount++)
   {
      // The current random e value
      auto_BN e_value;
      VHInternal::rand_range(qm, rs, e_value);
      //VHUtil::cout() << "e_value is " << e_value << std::endl;
      e_vec.push_back(e_value);
      add_BN_element(root_e_values, "e_value", e_value, DEC);
   }
   // A stream to hold the e values
   std::ostringstream oss_e_values;
   oss_e_values << xml_e_values;
      
   // For each ballot, multiply all X values together to get Xhat
   // For each ballot, multiply all Y values together to get Yhat
   // For each ballot, multiply all Xbar values together to get Xcheck
   // For each ballot, multiply all Ybar values together to get Ycheck
      
   for (int i=0; i<ksize; i++)
   {
      // The X values for the current ballot
      VHUtil::xml_node current_X_set = root_Xvalues->e(BALLOT, i);
      // The Y values for the current ballot
      VHUtil::xml_node current_Y_set = root_Yvalues->e(BALLOT, i);
      // The Xbar values for the current ballot
      VHUtil::xml_node current_Xbar_set = root_Xvalues_out->e(BALLOT, i);
      // The Ybar values for the current ballot
      VHUtil::xml_node current_Ybar_set = root_Yvalues_out->e(BALLOT, i);
      // The final product of the X components for this ballot
      auto_BN X_hat;
      VH_nonzero(BN_one(X_hat), BN_ONE);
      // The final product of the Y components for this ballot
      auto_BN Y_hat;
      VH_nonzero(BN_one(Y_hat), BN_ONE);
         
      // The final product of the Xbar components for this ballot
      auto_BN X_check;
      VH_nonzero(BN_one(X_check), BN_ONE);
      // The final product of the Ybar components for this ballot
      auto_BN Y_check;
      VH_nonzero(BN_one(Y_check), BN_ONE);
      for (icount=0; icount<num_questions; icount++)
      {
         // The current X value
         auto_BN current_X = xml2BN(current_X_set->e(X_VALUE, icount));
         // The current Y value
         auto_BN current_Y = xml2BN(current_Y_set->e(Y_VALUE, icount));
         // The current Xbar value
         auto_BN current_Xbar =
            xml2BN(current_Xbar_set->e(X_VALUE, icount));
         // The current Ybar value
         auto_BN current_Ybar =
            xml2BN(current_Ybar_set->e(Y_VALUE, icount));
            
         // X^e
         auto_BN X_exp;
         // Y^e
         auto_BN Y_exp;
         // Xbar^e
         auto_BN Xbar_exp;
         // Ybar^e
         auto_BN Ybar_exp;
            
         VH_nonzero(BN_mod_exp(X_exp, current_X, e_vec[icount], pm, ctx), BN_MOD_EXP);
         VH_nonzero(BN_mod_exp(Y_exp, current_Y, e_vec[icount], pm, ctx), BN_MOD_EXP);
         VH_nonzero(BN_mod_mul(X_hat, X_hat, X_exp, pm, ctx), BN_MOD_MUL);
         VH_nonzero(BN_mod_mul(Y_hat, Y_hat, Y_exp, pm, ctx), BN_MOD_MUL);
            
         VH_nonzero(BN_mod_exp(Xbar_exp, current_Xbar, e_vec[icount], pm, ctx), BN_MOD_EXP);
         VH_nonzero(BN_mod_exp(Ybar_exp, current_Ybar, e_vec[icount], pm, ctx), BN_MOD_EXP);
         VH_nonzero(BN_mod_mul(X_check, X_check, Xbar_exp, pm, ctx), BN_MOD_MUL);
         VH_nonzero(BN_mod_mul(Y_check, Y_check, Ybar_exp, pm, ctx), BN_MOD_MUL);
      }
         
      add_BN_element(root_Xhats, X_VALUE, X_hat, DEC);
      add_BN_element(root_Yhats, Y_VALUE, Y_hat, DEC);
      add_BN_element(root_Xchecks, X_VALUE, X_check, DEC);
      add_BN_element(root_Ychecks, Y_VALUE, Y_check, DEC);
   }

   // Streams to hold the output values
   std::ostringstream oss_Xhats;
   std::ostringstream oss_Yhats;
   std::ostringstream oss_Xchecks;
   std::ostringstream oss_Ychecks;
      
   oss_Xhats << xml_Xhats;
   oss_Yhats << xml_Yhats;
   oss_Xchecks << xml_Xchecks;
   oss_Ychecks << xml_Ychecks;

   *X_hats = VHTI_dup(oss_Xhats.str().c_str());
   *Y_hats = VHTI_dup(oss_Yhats.str().c_str());
   *X_checks = VHTI_dup(oss_Xchecks.str().c_str());
   *Y_checks = VHTI_dup(oss_Ychecks.str().c_str());
   *e_values = VHTI_dup(oss_e_values.str().c_str());
}
