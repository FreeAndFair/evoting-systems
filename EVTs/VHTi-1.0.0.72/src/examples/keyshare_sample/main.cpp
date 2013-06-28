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

#include <vhti/keyshare_util.h>
#include <vhti/gen_seccoeff.h>
#include <vhti/gen_broadcast.h>
#include <vhti/gen_pubkey.h>
#include <vhti/gen_secrets.h>
#include <vhti/gen_comm.h>
#include <vhti/random.h>
#include <vhti/check_comm.h>
#include <vhti/support.h>
#include <vhti/types.h>
#include "misc/xml_tree.h"
#include "misc/vh_cout.h"

#include <string>
#include <sstream>

int
main (int argc, char *argv[]) // n, t are command line parameters
{
   int result = 0;

   // default values
   char *numAuth = "4";
   char *thrAuth = "3";

   if (argc > 1)
   {
      numAuth = argv[1];
      if (argc > 2)
      {
         thrAuth = argv[2];
      }
   }

   int na = 0;
   {
      std::istringstream s_na(numAuth);
      s_na >> na;
   }
   int th = 0;
   {
      std::istringstream s_th(thrAuth);
      s_th >> th;
   }

   try {
   printf("Creating key generation parameters ... please wait ...\n");
   // Create key gen parameters
   auto_freeing<KeyGenParameters> key_gen_parameters = 0;
   VHUtil::xml_tree xml_seed("<SeedParameters/>");
   xml_seed.root ()->new_element(NUM_AUTH)->add_characters(numAuth);
   xml_seed.root ()->new_element(THRESHOLD)->add_characters(thrAuth);


   VHUtil::cout() << "xml_seed is " << xml_seed << std::endl;
   char * in_kgp = VHTI_dup(xml_seed.str().c_str());

   std::string key("<RandomSeedKey>Some random string to hash for a random block.</RandomSeedKey>");
   //std::string key("<RandomSeedKey>The quick brown fox jumps over the lazy dog.</RandomSeedKey>");
   auto_freeing<RandomState> random_state = 0;
   result = VHTI_generate_random_state(key.c_str(), &random_state);

   if (result)
   {
      printf("\n\nVHTI_generate_random_state failed!");
      exit(1);
   }

   VHUtil::xml_tree xml_auths("<Authorities/>");
   VHUtil::xml_tree xml_all_scs("<AllSecretCoefficients/>");
   VHUtil::xml_tree xml_all_bvs("<BroadcastValues/>");
   VHUtil::xml_node root_auths = xml_auths.root();
   VHUtil::xml_node root_all_scs = xml_all_scs.root();
   VHUtil::xml_node root_all_bvs = xml_all_bvs.root();

   // Create key_gen_parameters
   auto_freeing<RandomState> return_random_state = 0;
   result = VHTI_create_keygen_parameters(in_kgp, random_state, &key_gen_parameters,
                                          &return_random_state);
   if (result)
   {
      printf("\n\nVHTI_create_keygen_parameters failed!");
      exit(1);
   }

   random_state = VHTI_dup(return_random_state);
         
   printf("Creating %d authority objects.\n", na);
   // Create authority_id blobs, generate secret coefficients and broadcast values
         
   for (int i=0; i<na; i++)
   {
      auto_freeing<Authority> authority = 0;
      {
         std::ostringstream oss;
         oss << i;

         auto_freeing<GeneralPurposePrivateKey> pr = 0;
         VHTI_create_authority(oss.str().c_str(),
                               key_gen_parameters,
                               random_state,
                               0,
                               &pr,
                               & authority,
                               &return_random_state);
      }
      random_state = VHTI_dup(return_random_state);

      VHUtil::xml_tree xml_auth((char *)authority);
      root_auths->add_element(xml_auth.root()->deep_copy());
            
      auto_freeing<SecretCoefficients> secret_coefficients = 0;
      printf("Generating secret coefficients for authority %d.\n", i);
            
      result = VHTI_generate_secret_coefficients(key_gen_parameters, authority,
                                                 random_state, &secret_coefficients, &return_random_state);

      if (result)
      {
         printf("VHTI_generate_secret_coefficients failed!\n");
         exit(1);
      }
            
      printf("\tSuccess!\n");

      random_state = VHTI_dup(return_random_state);               

      VHUtil::xml_tree xml_sc((char *)secret_coefficients);
      root_all_scs->add_element(xml_sc.root()->deep_copy());
               
      auto_freeing<BroadcastValue> broadcast_value = 0;
      printf("Generating broadcast values for authority %d.\n", i);
               
      result = VHTI_generate_broadcast(key_gen_parameters, secret_coefficients,
                                       random_state, &broadcast_value, &return_random_state);

      if (result)
      {
         printf("VHTI_generate_broadcast failed!\n");
         exit(1);
      }

      printf("\tSuccess!\n");
      random_state = VHTI_dup(return_random_state);

      VHUtil::xml_tree xml_bv((char *)broadcast_value);
      root_all_bvs->add_element(xml_bv.root()->deep_copy());
   }
         
   VHUtil::cout() << "KEYGEN PARAMETERS" << std::endl;
   std::string str_kgp(key_gen_parameters);
   VHUtil::cout() << str_kgp << std::endl;
   VHUtil::cout() << "AUTHORITIES" << std::endl;
   VHUtil::cout() << xml_auths << std::endl;
   VHUtil::cout() << "SECRET COEFFICIENTS" << std::endl;
   VHUtil::cout() << xml_all_scs << std::endl;
   VHUtil::cout() << "BROADCAST VALUES" << std::endl;
   VHUtil::cout() << xml_all_bvs << std::endl;


   // Now we can generate the public key
   ////char *all_broadcast_values = 0;
   std::ostringstream all_bvs_stream;
   all_bvs_stream << xml_all_bvs;

   auto_freeing<ElectionPublicKey> public_key = 0;
   printf("Generating public key.\n");
   result = VHTI_generate_public_key(key_gen_parameters, all_bvs_stream.str().c_str(),
                                     &public_key);
   if (result)
   {
      printf("VHTI_generate_public_key failed!\n");
      exit(1);
   }

   printf("\tSuccess!\n");

   VHUtil::cout() << "ELECTION PUBLIC KEY" << std::endl;
   std::string ePublicKey(public_key);
   VHUtil::cout() << ePublicKey << std::endl;

   VHUtil::xml_tree xml_all_pss("<AllPairwiseSecrets/>");
   VHUtil::xml_node root_all_pss = xml_all_pss.root();

   // Generate secrets
   for (int from_id=0; from_id<na; from_id++)
   {
      // Find the FromID authority's secret coefficients
      std::ostringstream fromid_stream;
      fromid_stream << from_id;

      VHUtil::xml_node xml_sc = root_all_scs->e(SECRET_COEFFICIENTS,
                                                AUTH_FINGERPRINT,
                                                fromid_stream.str());

      std::ostringstream sc_stream;
      sc_stream << *xml_sc;

      // Calculate pairwise secrets
      for (int to_id=0; to_id<na; to_id++)
      {
         std::ostringstream toid_stream;
         toid_stream << to_id;
         VHUtil::xml_node node_to_id = root_auths->e(AUTHORITY,
                                                     AUTH_FINGERPRINT,
                                                     toid_stream.str());

         std::ostringstream auth_stream;
         auth_stream << *node_to_id;

         auto_freeing<PairwiseSecret> pairwise_secret = 0;
         printf("Generating pairwise secret from authority %d to authority %d.\n", from_id, to_id);
         result = VHTI_generate_secret(key_gen_parameters, auth_stream.str().c_str(),
                                       sc_stream.str().c_str(), &pairwise_secret);

         if (result)
         {
            printf("VHTI_generate_secret failed!\n");
            exit(1);
         }

         printf("\tSuccess!\n");
         VHUtil::xml_tree xml_ps((char *)pairwise_secret);
         root_all_pss->add_element(xml_ps.root()->deep_copy());
      }
   }

   VHUtil::cout() << "PAIRWISE SECRETS" << std::endl;
   VHUtil::cout() << xml_all_pss << std::endl;

   // Generate commitments and secret shares
   // First we need to separate out the pairwise secrets for each authority
   for (i=0; i<na; i++)
   {
      std::ostringstream toid_stream;
      toid_stream << i;

      // Get the AuthCertFingerprint object
      VHUtil::xml_node node_to_id = root_auths->e(AUTHORITY,
                                                  AUTH_FINGERPRINT,
                                                  toid_stream.str());

      std::ostringstream auth_stream;
      auth_stream << *node_to_id;

      VHUtil::xml_tree xml_pss("<PairwiseSecrets/>");
      VHUtil::xml_node root_pss = xml_pss.root();

      int num_elems = root_all_pss->element_count();
      for (int j=0; j<num_elems; j++)
      {
         VHUtil::xml_node current_node = root_all_pss->e(j);
         if (current_node->attribute(TO_ID) == toid_stream.str())
         {
            root_pss->add_element(current_node->deep_copy());
         }
      }

      // Now we have the secrets TO authority i
      std::ostringstream toid_secrets_stream;
      toid_secrets_stream << xml_pss;

      std::ostringstream all_bvs_stream;
      all_bvs_stream << xml_all_bvs;

      auto_freeing<SecretShare> secret_share = 0;
      auto_freeing<KeyShareCommitment> keyshare_commitment = 0;
      printf("Generating secret share and key share commitment for authority %d.\n", i);
      result = VHTI_generate_commitment(key_gen_parameters, auth_stream.str().c_str(),
                                        all_bvs_stream.str().c_str(), toid_secrets_stream.str().c_str(),
                                        &secret_share, &keyshare_commitment);

      if (result)
      {
         printf("VHTI_generate_commitment failed!\n");
         exit(1);
      }

      printf("\tSuccess!\n");
      // Check commitment we just made
      printf("Checking key share commitment for authority %d.\n", i);

      auto_freeing<CheckResults> check_comm_result = 0;
      result = VHTI_check_commitment(key_gen_parameters, auth_stream.str().c_str(),
                                     all_bvs_stream.str().c_str(), keyshare_commitment, &check_comm_result);

      if (result
          ||
          !strstr(check_comm_result, CHECK_SUCCESS_TEXT))
      {
         printf("\tFailure!\n");
         if (!result)
            printf("%s\n", check_comm_result);
         exit(1);
      }

      printf("\tSuccess!\n");
      VHUtil::cout() << "SECRET SHARE" << std::endl;
      VHUtil::cout() << (const char *) secret_share << std::endl;
      VHUtil::cout() << "KEY SHARE COMMITMENT" << std::endl;
      VHUtil::cout() << (const char *) keyshare_commitment << std::endl;
   }

   ::free(in_kgp);

   }
   catch (...)
   {
      printf("Caught exception; sorry\n");
      exit(1);
   }
   
   printf("\n\nKey Sharing sample FINISHED EXECUTING.\n");
   return 0;
}
