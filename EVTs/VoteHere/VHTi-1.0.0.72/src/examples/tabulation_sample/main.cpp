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

#include "vhti/auth.h"
#include "vhti/partial_decrypt.h"
#include "vhti/check_partial_decrypt.h"
#include "vhti/check_pds_and_combine.h"
#include "vhti/check_vc_pds_and_combine.h"
#include "vhti/random.h"
#include "vhti/shuffle.h"
#include "vhti/support.h"
#include "vhti/check_shuffle.h"
#include "vhti/gen_pre_verification_results.h"
#include "vhti/gen_pv_results.h"
#include "vhti/types.h"
#include "misc/file_contents.h"
#include "misc/vh_cout.h"
#include "misc/xml_tree.h"
#include "misc/safe_xml_tree.h"
#include "misc/vh_excpt.h"

#include <string>
#include <sstream>
#include <fstream>
#include <iostream>

#include <direct.h>

int
main()
{
   int result = 0;

   {
     char buf [1024];
     std::cout << "My cwd is "
               << getcwd(buf, sizeof (buf))
               << std::endl;
   }

   try {
      // voting
      const std::string svbs (VHUtil::file_contents ("../../vhti/bindings/perl/examples/svbs.xml"));

      const std::string ballot_signing_key  (VHUtil::file_contents ("../../vhti/bindings/perl/examples/pollsite-pubkey.xml"));
      const std::string signed_blank_ballot (VHUtil::file_contents ("../../vhti/bindings/perl/examples/sbb.xml"));

      // <- authenticate <- svbs, voter roll, blank ballot
      std::string raw_ballot_box;
      {
         VHUtil::safe_xml_tree xml_sbb (signed_blank_ballot, BLANK_BALLOT, ballot_signing_key);
         auto_freeing<RawBallotBox> tmp = 0;
         std::ostringstream bb_stream;
         bb_stream << *(xml_sbb.root ());
         result = VHTI_authenticate (svbs.c_str (),
                                     (static_cast<std::string>(VHUtil::file_contents ("../../vhti/bindings/perl/examples/voter-roll.xml"))).c_str (),
                                     bb_stream.str ().c_str (),
                                     &tmp);
         if (!result)
            raw_ballot_box = std::string (tmp);
      }

      VHUtil::xml_tree xml_vvks       (VHUtil::file_contents ("../../vhti/bindings/perl/examples/DRE/vvks.xml"));
      VHUtil::xml_tree xml_comm_auth_0 (VHUtil::file_contents ("../../vhti/bindings/perl/examples/committed-auth-0.xml"));
      VHUtil::xml_node root_auth_0 = xml_comm_auth_0.root();
      VHUtil::xml_tree xml_comm_auth_1 (VHUtil::file_contents ("../../vhti/bindings/perl/examples/committed-auth-1.xml"));
      VHUtil::xml_node root_auth_1 = xml_comm_auth_1.root();
      VHUtil::xml_tree xml_comm_auths("<CommittedAuthorities/>");
      VHUtil::xml_node root_comm_auths = xml_comm_auths.root();
      root_comm_auths->add_element(root_auth_0->deep_copy());
      root_comm_auths->add_element(root_auth_1->deep_copy());

      VHUtil::xml_tree xml_ss_0 (VHUtil::file_contents ("../../vhti/bindings/perl/examples/auth0/secret-share.xml"));
      VHUtil::xml_node root_ss_0 = xml_ss_0.root();
      VHUtil::xml_tree xml_ss_1 (VHUtil::file_contents ("../../vhti/bindings/perl/examples/auth1/secret-share.xml"));
      VHUtil::xml_node root_ss_1 = xml_ss_1.root();
      VHUtil::xml_tree xml_sss("<SecretShares/>");
      VHUtil::xml_node root_sss = xml_sss.root();
      root_sss->add_element(root_ss_0->deep_copy());
      root_sss->add_element(root_ss_1->deep_copy());


      // Make a PDBB container to use in combine decrypts function
      VHUtil::xml_tree xml_pdbb("<PartiallyDecryptedBallotBox/>");
      VHUtil::xml_node root_pdbb = xml_pdbb.root();

      VHUtil::xml_tree xml_auth_pds("<AuthorityPartialDecrypts/>");
      VHUtil::xml_node root_auth_pds = xml_auth_pds.root();

      // Make a random state object
      std::string key("<RandomSeedKey>Some random string to hash for a random block.</RandomSeedKey>");
      auto_freeing<RandomState> random_state = 0;
      result = VHTI_generate_random_state(key.c_str(), &random_state);
      if (result)
      {
         printf("Generating a random state failed.\n\n");
         exit(1);
      }
      auto_freeing<RandomState> return_random_state = 0;

      auto_freeing<RawBallotBox> raw_ballot_box_after = 0;
      auto_freeing<ShuffleValidityProof> shuffle_validity_proof = 0;

      for (int kk=0; kk<3; kk++)
      {
         // Shuffle ballots
         printf("\n\nShuffling Ballots");
         result = VHTI_shuffle(raw_ballot_box.c_str(), random_state,
                               signed_blank_ballot.c_str(),
                               ballot_signing_key.c_str (),
                               &raw_ballot_box_after, &return_random_state,
                               &shuffle_validity_proof);
         random_state = VHTI_dup(return_random_state);

         if (result)
         {
            printf("Uh oh, the shuffle proof code failed.\n\n");
            exit(1);
         }

         printf("    \n\nSuccess!\n");
         printf("The shuffle validity proof is complete.\n\n");
         printf("The Shuffle Validity Proof is as follows:\n\n");
         printf("%s", shuffle_validity_proof);
         std::string str_svp(shuffle_validity_proof);
         //VHUtil::cout() << "Shuffle Validity Proof " << str_svp << std::endl;

         // Check shuffle validity proof
         printf("\n\nChecking the Shuffle");
         auto_freeing<CheckResults> check_shuffle_result = 0;
         result = VHTI_check_shuffle(raw_ballot_box.c_str(), raw_ballot_box_after, signed_blank_ballot.c_str(),
                                     ballot_signing_key.c_str (),
                                     shuffle_validity_proof, &check_shuffle_result);

         if ((!result)
             &&
             strstr (check_shuffle_result, CHECK_SUCCESS_TEXT))
         {
            printf("    \n\nSuccess!\n");
            printf("The shuffle validity proof checking is complete.\n\n");
         }
         else
         {
            printf("\n\nUh oh, the shuffle proof checking code failed.\n\n");
            exit(1);
         }

      } //kk

      // Put the Shuffled RBB in the PartiallyDecryptedBallotBox
      std::string str_rbb_after(raw_ballot_box_after);
      VHUtil::xml_tree xml_rbb_after(str_rbb_after);
      VHUtil::xml_node root_rbb_after = xml_rbb_after.root();
      root_pdbb->add_element(root_rbb_after->deep_copy());

      if (!result)
      {
         int num_auths_elems = xml_comm_auths.root ()->element_count();
         for (int i=0; i<num_auths_elems; i++)
         {
            VHUtil::xml_node node_comm_auth = root_comm_auths->e(i);
            VHUtil::xml_node node_auth = node_comm_auth->e(AUTHORITY);
            std::string authID = node_auth->attribute(AUTH_FINGERPRINT);
         
            std::ostringstream comm_auth_stream; 
            comm_auth_stream << *node_comm_auth;    
         
            VHUtil::xml_node node_ss = root_sss->e(i);  // Assume same # of elements
            std::ostringstream secret_stream;
            secret_stream << *node_ss;
         
            printf("Partial decryption of raw ballot box by authority %s.\n", authID.c_str());

            auto_freeing<AuthorityPartialDecrypt> auth_partial_decrypt = 0;
            result = VHTI_partial_decrypt(raw_ballot_box_after, signed_blank_ballot.c_str(),
                                          ballot_signing_key.c_str (),
                                          comm_auth_stream.str().c_str(),
                                          secret_stream.str().c_str(), random_state,
                                          &auth_partial_decrypt, &return_random_state);

            if (result)
            {
               printf("    Partial decryption by authority %s failed.\n", authID.c_str());
               exit(1);
            }

            random_state = VHTI_dup(return_random_state);
            printf("    Success!\n");
            VHUtil::xml_tree xml_auth_pd((char *)auth_partial_decrypt);
            VHUtil::xml_node root_auth_pd = xml_auth_pd.root();
            std::ostringstream auth_pd_stream;
            auth_pd_stream << xml_auth_pd;
            
            root_auth_pds->add_element(root_auth_pd->deep_copy());

            // Check the Partial Decrypt
            printf("Checking partial decrypt.\n");
            auto_freeing<Results> check_partial_decrypt_result = 0;
            result = VHTI_check_partial_decrypt(raw_ballot_box_after,
                                                auth_partial_decrypt,
                                                signed_blank_ballot.c_str(), ballot_signing_key.c_str(),
                                                &check_partial_decrypt_result);

            if (result)
            {
               printf("    Check of partial decrypt FAILED !\n");
               exit(1);
            }

            printf("    Check of partial decrypt SUCCEEDED !\n");
            std::string strRBB (raw_ballot_box_after);
            std::string strAPD (auth_partial_decrypt);
            VHUtil::cout() << "RAW BALLOT BOX AFTER IS " << strRBB << std::endl;
            VHUtil::cout() << "AUTH PARTIAL DECRYPT IS " << strAPD << std::endl;
         }
      }

      // Put the AuthorityPartialDecrypts into the PartiallyDecryptedBallotBox
      root_pdbb->add_element(root_auth_pds->deep_copy());

      printf("\nPartial decryption and checking by all authorities is successfully complete.\n\n");
      printf("The AuthorityPartialDecrypts are as follows:\n\n");
      std::ostringstream oss;
      oss << xml_auth_pds;
      printf("%s\n\n", oss.str().c_str());

      // Check partial decrypts and combine
      auto_freeing<ClearTextBallots> clear_text_ballots = 0;
      auto_freeing<Results> combine_partial_decrypt_result = 0;

      std::ostringstream pdbb_stream;
      pdbb_stream << xml_pdbb;

      VHUtil::cout() << "xml_pdbb is " << xml_pdbb << std::endl;
      
      printf("\n\nChecking each partial decrypt, then combining them.\n");

      result = VHTI_check_partial_decrypts_and_combine
         (signed_blank_ballot.c_str(), ballot_signing_key.c_str (),
          pdbb_stream.str().c_str(),
          &clear_text_ballots, &combine_partial_decrypt_result);

      if (!result
          &&
          strstr(combine_partial_decrypt_result, CHECK_SUCCESS_TEXT))
      {
         printf("    Success!\n");
         printf("Combined decryption by all authorities is complete.\n\n");
         printf("The Clear Text Ballots are as follows:\n\n");
         printf("%s", clear_text_ballots);
      }
      else
      {
         printf("Failure to complete combined decryption successfully.\n\n");
         exit(1);
      }

      std::string str_ctb(clear_text_ballots);

      VHUtil::xml_tree xml_pvc_boxes("<PreVerificationCodeBoxes/>");
      VHUtil::xml_node root_pvc_boxes = xml_pvc_boxes.root();

      int num_auths_elems = xml_comm_auths.root ()->element_count();
      for (int i=0; i<num_auths_elems; i++)
      {
         // Generate PreVerificationCodes
         VHUtil::xml_node current_vvk = xml_vvks.root ()->e(i);
         std::ostringstream oss_vvk;
         oss_vvk << *current_vvk;
         auto_freeing < PreVerificationCodeBox > pre_vcode_box = 0;
         result = VHTI_generate_pre_verification_results (oss_vvk.str().c_str(), svbs.c_str(),
                                                          signed_blank_ballot.c_str(),
                                                          ballot_signing_key.c_str (),
                                                          &pre_vcode_box);
         if (result)
         {
            printf("\n\nGenerating pre-verification results failed.\n");
            exit(1);
         }

         printf("\n\nPreVerificationResults for authority %d is :\n", i );
         printf("%s", pre_vcode_box);

         std::string str_pvc(pre_vcode_box);
         VHUtil::xml_tree xml_pvc(str_pvc);
         VHUtil::xml_node root_pvc = xml_pvc.root();

         // Add these PreVerificationCodes to collection from all trustees
         root_pvc_boxes->add_element(root_pvc->deep_copy());
      }
      
      VHUtil::xml_tree xml_auth_pds_for_vcodes("<AuthorityPartialDecrypts/>");
      VHUtil::xml_node root_auth_pds_for_vcodes = xml_auth_pds_for_vcodes.root();

      std::ostringstream oss_pvc_boxes;
      oss_pvc_boxes << xml_pvc_boxes;
      VHUtil::cout() << "pre_vcode_boxes is " << xml_pvc_boxes << std::endl;

      // Each authority takes all of the verification codes and multiplies them
      // together, then does a partial decrypt
         
      num_auths_elems = xml_comm_auths.root ()->element_count();
      for (i=0; i<num_auths_elems; i++)
      {
         VHUtil::xml_node node_comm_auth = root_comm_auths->e(i);
         VHUtil::xml_node node_auth = node_comm_auth->e(AUTHORITY);
         std::string authID = node_auth->attribute(AUTH_FINGERPRINT);
            
         std::ostringstream comm_auth_stream; 
         comm_auth_stream << *node_comm_auth;    
            
         VHUtil::xml_node node_ss = root_sss->e(i);  // Assume same # of elements
         std::ostringstream secret_stream;
         secret_stream << *node_ss;
            
         printf("\n\nPartial decryption of Vote Verification Codes by authority %s.\n", authID.c_str());
            
         auto_freeing< AuthorityPartialDecrypt > auth_partial_decrypt_of_verifications = 0;
         result = VHTI_generate_partial_verification_results
            (oss_pvc_boxes.str().c_str(),
             signed_blank_ballot.c_str(),
             ballot_signing_key.c_str (),
             comm_auth_stream.str().c_str(),
             secret_stream.str().c_str(), random_state,
             &auth_partial_decrypt_of_verifications, &return_random_state);
         if (!result)
         {
            random_state = VHTI_dup(return_random_state);
            printf("    Success!\n");
            VHUtil::xml_tree xml_auth_pd((char *)auth_partial_decrypt_of_verifications);
            VHUtil::xml_node root_auth_pd = xml_auth_pd.root();
            std::ostringstream auth_pd_stream;
            auth_pd_stream << xml_auth_pd;
               
            root_auth_pds_for_vcodes->add_element(root_auth_pd->deep_copy());
         }
         else
         {
            printf("    Partial decryption of Vote Verification Codes by authority %s failed.\n", authID.c_str());
            exit(1);
         }
      }

      std::ostringstream oss_auth_pds_vc;
      oss_auth_pds_vc << xml_auth_pds_for_vcodes;
      VHUtil::cout() << "xml_auth_pds_for_vcodes is " << xml_auth_pds_for_vcodes << std::endl;

      // Check partial decrypts and combine

      int string_len = 32;
      VHUtil::xml_tree xml_enc("<AlphabetEncoding/>");
      VHUtil::xml_node root_enc = xml_enc.root();
      root_enc->add_characters("DEC");  // DEC indicates a Decimal alphabet
      std::ostringstream enc_oss;
      enc_oss << xml_enc;

      printf("\n\nChecking each partial decrypt of verification codes, then combining them.\n");
      result = VHTI_check_vcode_partial_decrypts_and_combine(oss_pvc_boxes.str().c_str(),
                                                             oss_auth_pds_vc.str().c_str(),
                                                             svbs.c_str (),
                                                             signed_blank_ballot.c_str(),
                                                             ballot_signing_key.c_str (),
                                                             string_len,
                                                             enc_oss.str().c_str(),
                                                             &clear_text_ballots,
                                                             &combine_partial_decrypt_result);
         
      if (!result
          &&
          strstr(combine_partial_decrypt_result, CHECK_SUCCESS_TEXT))
      {
         printf("    Success!\n");
         printf("Combined decryption of Vote Verification Codes by all authorities is complete.\n\n");
         printf("The Clear Text Ballots are as follows:\n\n");
         printf("%s", clear_text_ballots);
         std::string str_ctb(clear_text_ballots);
      }
      else
      {
         printf("Failure to complete combined decryption successfully.\n\n");
         exit(1);
      }

      printf("\n\nTabulation sample FINISHED EXECUTING.\n");
   }
   catch (VHUtil::Exception & e)
   {
      std::cerr << "Caught exception: " << e << std::endl;
      if (ENOENT == e.getResultNo())
        {
          std::cerr << "You probably need to run the Perl examples; I get all my input data from them. " << std::endl;
        }
      result = 1;
   }
   catch (std::string &e)
   {
      std::cerr << "Caught exception: " << e << std::endl;
      result = 1;
   }
   catch (...)
   {
      std::cerr << "Caught unknown exception" << std::endl;
      result = 1;
   }

   return result;
}
