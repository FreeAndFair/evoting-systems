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

#include <vhti/genkeys.h>
#include <vhti/crypt.h>
#include <vhti/sign.h>
#include <misc/xml_tree.h>
#include <misc/vh_cout.h>

#include <string>
#include <sstream>

int
main (int argc, char *argv[])
{
   int result = 0;

   {
      void * foo = ::malloc(10);
      ::free(foo);
   }

   std::string io("<IdentInfo>your name</IdentInfo>");

   auto_freeing<GeneralPurposePrivateKey> Prvkey = 0;
   auto_freeing<GeneralPurposePublicKey>  Pubkey = 0;

   result = VHTI_generate_keys(io.c_str(),
                               &Prvkey,
                               &Pubkey);

   if (!result)
   {
      auto_freeing<ConstCharStar> signed_xml = 0;

      const std::string sign_me  ("<IdentInfo>Hello World</IdentInfo>");

      printf ("Signing %s\n\n", sign_me.c_str ());
      result = VHTI_sign_xml(Prvkey, sign_me.c_str(), &signed_xml);
         
      VHUtil::cout () << "VHTI_sign returned " << result << std::endl;
         
      if (!result)
      {
         printf("    Woo hoo.  Signing succeeded.\n\n");
         std::string str_sd(signed_xml);
         VHUtil::cout() << "Signed_Xml is " << str_sd << std::endl;

         auto_freeing<CheckResults> c_res = 0;
            
         auto_freeing<ConstCharStar> inner_xml = 0;
         result = VHTI_check_xml(Pubkey,
                                 signed_xml,
                                 IDENT_INFO,
                                 & c_res,
                                 & inner_xml);
            
         if (!result)
         {
            if (::strstr(c_res, CHECK_SUCCESS_TEXT))
            {
               printf("\n    Woo hoo.  Signed_Xml checked");
               if (0 == ::strcmp (inner_xml,
                                  sign_me.c_str ()))
                  printf (" ... and the inner XML is just what we signed.\n\n");
               else
               {
                  printf ("   Uh oh.  inner XML was %s but we signed %s.\n\n",
                          inner_xml,
                          sign_me.c_str ());
                  exit(1);
               }
            }
            else
            {
               printf("\n    Gol durn it!.  Signed_Xml didn't check.\n\n");
               exit(1);
            }
         }
         else
         {
            printf("    Uh oh.  Couldn't determine if the signed_xml checks.\n\n");
            exit(1);
         }
      }
      else
      {
         printf("    Uh oh.  Signing failed.\n\n");
         exit(1);
      }

      std::string io2("Hello World 2");

      printf("Encrypting %s\n\n", io2.c_str());
      auto_freeing<EncryptedData> encrypted_data = 0;
      result = VHTI_encrypt(Pubkey, io2.c_str(), &encrypted_data);
         
      if (!result)
      {
         printf("\n    Woo hoo.  Encryption worked.\n\n");
         std::string str_ed(encrypted_data);
         VHUtil::cout() << "encrypted_data is " << str_ed << std::endl;
            
         auto_freeing<ConstCharStar> plaintext = 0;
         result = VHTI_decrypt(Prvkey, encrypted_data, &plaintext);
            
         if (!result)
         {            
            printf("    Woo hoo.  Decryption worked.\n\n");
            std::string str_pt(plaintext);
         }
         else
         {
            printf("    Uh oh.  Decryption didn't work.\n\n");
            exit(1);
         }
      }
      else
      {
         printf("    Uh oh.  Encryption didn't work.\n\n");
      }
   }
   else
   {
      printf("    Uh oh.  VHTI_generate_keys failed.\n\n");
   }

   // Now encrypt and decrypt using a password
   std::string iopw("Hello World with a password");
   std::string passwd("<Password>Shhhh</Password>");
   
   printf("Encrypting: %s\n\n", iopw.c_str());
   auto_freeing<PasswordEncryptedData> encrypted_data = 0;
   result = VHTI_password_encrypt(passwd.c_str(), iopw.c_str(), &encrypted_data);
   
   if (!result)
   {
      printf("\n    Woo hoo.  Password encryption worked.\n\n");
      std::string str_ed(encrypted_data);
      printf("encrypted_data is:\n %s\n\n", encrypted_data);
      
      auto_freeing<ConstCharStar> plaintext = 0;
      result = VHTI_password_decrypt(passwd.c_str(), encrypted_data, &plaintext);
      
      if (!result)
      {   
         printf("    Woo hoo.  Password decryption worked.\n\n");
         std::string str_pt(plaintext);
         printf("plaintext is: %s\n\n", plaintext);
      }
      else
      {
         printf("    Uh oh.  Password decryption didn't work.\n\n");
         exit(1);
      }
   }
   else
   {
      printf("    Uh oh.  Password encryption didn't work.\n\n");
      exit(1);
   }

   printf("\n\nPublic Key Infrastructure sample FINISHED EXECUTING.\n");
   return 0;
}
