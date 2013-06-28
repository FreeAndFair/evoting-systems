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

#include "vhti/check_dictionary_secrets.h"
#include "vhti/sign.h"
#include "vhti/random.h"
#include <support/support_internal.h>
#include <support/internal_error.h>
#include <support/random_internal.h>
#include <support/bignum.h>
#include <support/xml_tree_group_check.h>
#include <misc/vh_excpt.h>
#include <misc/xml_tree.h>
#include <string>
#include <sstream>

// Anybody can call this function using any of the commitments
// to check the revealed secrets

int
VHTI_check_dictionary_secrets (TrusteeRevealedDictionarySecrets trustee_dict_secrets,
                               SignedTrusteeDictionaryCommitments trustee_dict_comm,
                               GeneralPurposePublicKey tsig_pubkey,
                               BlankBallot blank_ballot,
                               CheckResults *check_dictionary_secrets_result)
{
   int result = 0; // Assume success until told otherwise
   int check_res = 0;
   auto_BN pm(NULL); // The Election Modulus
   auto_BN qm(NULL); // The Election Subgroup Modulus
   auto_BN gen(NULL); // The Election Subgroup Generator
   auto_BN ePublicKey(NULL); // The Election Public Key
   // An OpenSSL structure that holds BIGNUM temporary variables used by
   // library functions
   auto_BN_CTX ctx(BN_CTX_new());
   *check_dictionary_secrets_result = NULL;
   
   try
   {
      VH_nonzero (ctx, BN_CTX_NEW);
      
      VH_zero(::VHTI_validate(TRUSTEE_REVEALED_DICTIONARY_SECRETS, trustee_dict_secrets),
         VALIDATION_FALIURE);
      VH_zero(::VHTI_validate(SIGNED_TRUSTEE_DICTIONARY_COMMITMENTS, trustee_dict_comm),
         VALIDATION_FAILURE);
      VH_zero(::VHTI_validate(BLANK_BALLOT, blank_ballot),
         VALIDATION_FAILURE);

      // An empty xml tree to hold CheckResults
      VHUtil::xml_tree xml_res("<" CHECK_RESULTS "/>");
      VHUtil::xml_node root_res = xml_res.root();

      // An xml tree from the BlankBallot
      VHUtil::xml_tree_group_check xml_bb(blank_ballot, pm, qm, gen, ePublicKey);
      VHUtil::xml_node root_bb = xml_bb.root();

       // An xml tree from the TrusteeDictionaryCommitments
      VHUtil::xml_tree_group_check xml_tdcs(trustee_dict_comm,
         TRUSTEE_DICTIONARY_COMMITMENTS,
         tsig_pubkey,
         pm, qm, gen, ePublicKey);
      VHUtil::xml_node root_tdcs = xml_tdcs.root();

      // Make tree out of TrusteeRevealedDictionarySecrets
      VHUtil::xml_tree_group_check xml_tds(trustee_dict_secrets, pm, qm, gen, ePublicKey);
      VHUtil::xml_node root_tds = xml_tds.root();

      // Check that the secrets and the commitments are from the same Trustee
      auto_BN aep_from_secrets =
         xml2BN(root_tds->e(AUTHORITY)->e(AUTHORITY_EVALUATION_POINT));
      auto_BN aep_from_commitments =
         xml2BN(root_tdcs->e(AUTHORITY)->e(AUTHORITY_EVALUATION_POINT));
      if (BN_cmp(aep_from_secrets, aep_from_commitments))
      {
         // Non zero answer means they are not equal
         check_res = 1;
         root_res->add_characters("Secrets and Commitments not from the same Trustee");
      }

      // Check that g^secret = commitment for each question
      for (int i=0; !check_res && i<root_tds->element_count(); i++)
      {
         if ((root_tds->e(i)->name() != BSN_REVEALED_DICTIONARY_SECRETS)
             ||
             check_res)
         {
            continue;
         }

         auto_BN current_bsn = xml2BN(root_tds->e(i)->e(BALLOT_SEQUENCE_NUMBER));
            
         // Find the corresponding BSNDictionaryCommitments in xml_tdcs
         for (int j=0; j<root_tdcs->element_count(); j++)
         {
            if ((root_tdcs->e(j)->name() != BSN_DICTIONARY_COMMITMENTS)
                ||
                check_res)
            {
               continue;
            }

            auto_BN test_bsn = xml2BN(root_tdcs->e(j)->e(BALLOT_SEQUENCE_NUMBER));

            if (BN_cmp(current_bsn, test_bsn))
            {
               continue;
            }

            // These are the commitments we want.  Just step through in order.
            for (int ii=0; ii<root_tdcs->e(j)->element_count(); ii++)
            {
               if ((root_tdcs->e(j)->e(ii)->name() != DICTIONARY_COMMITMENT)
                   ||
                   check_res)
               {
                  continue;
               }

               auto_BN comm_value = xml2BN(root_tdcs->e(j)->e(ii));
               auto_BN secret_value = xml2BN(root_tds->e(i)->e(ii));
               auto_BN g_exp;
               VHInternal::fixed_mod_exp(g_exp, gen, secret_value, pm, ctx);
               check_res = BN_cmp(g_exp, comm_value);
               if (0 == check_res)
               {
                  continue;
               }

               root_res->add_characters("Revealed Dictionary Secrets Check Failure");
            }
         }
      }
      if (check_res == 0)
      {
         root_res->add_characters("Revealed Dictionary Secrets Check Success");
      }
      std::ostringstream oss;
      oss << xml_res;
      *check_dictionary_secrets_result = VHTI_dup(oss.str().c_str());
   }
   catch (const VHUtil::Exception & e)
   {
      VHTI_set_last_error(e);
      result = e.getResultNo();
   }
   return result;
}
