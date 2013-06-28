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

#include "vhti/enc_ballot_pollsite.h"
#include "vhti/gen_vvkey.h"
#include "vhti/gen_vvdict.h"
#include "vhti/gen_vote_receipt_data.h"
#include "vhti/sign_receipt.h"
#include "vhti/sign.h"
#include "vhti/genkeys.h"
#include "vhti/random.h"
#include "vhti/support.h"
#include "vhti/types.h"
#include "misc/vh_cout.h"
#include "misc/xml_tree.h"
#include "misc/safe_xml_tree.h"
#include "misc/file_contents.h"

#include <string>
#include <sstream>

int
main()
{
   int result = 0;

   {  // this forces linker to use MPATROL.LIB when it's on the link line
      void * foo = ::malloc(10);
      ::free(foo);
   }

   std::string blank_ballot (VHUtil::file_contents ("../bb.xml"));
   std::string vote_verification_keys(VHUtil::file_contents("../vvks.xml"));
   std::string PollsiteSigPrvkey(VHUtil::file_contents("../ballot-signing-prvkey.xml"));

   // Of course, these need to be kept in sync with the answer
   // references in ../bb.xml
   std::string ctb("<ClearTextBallot>"
                   "<AnswerReference>A0</AnswerReference>"
                   "<AnswerReference>A4</AnswerReference>"
                   "</ClearTextBallot>");

   // Generate DSA key pair
   std::string keytype;
   auto_freeing<RandomSeedKey> prvkey = 0;
   auto_freeing<RandomSeedKey> pubkey = 0;
   
   std::string io("<IdentInfo>your name</IdentInfo>");

   result = VHTI_generate_keys(io.c_str(),
                               &prvkey,
                               &pubkey);

   std::string str_pubkey(pubkey);
   VHUtil::cout() << "str_pubkey is " << str_pubkey << std::endl;

   int string_len = 32;
   VHUtil::xml_tree xml_enc("<" ALPHABET_ENCODING "/>");
   VHUtil::xml_node root_enc = xml_enc.root();
   root_enc->add_characters("DEC");  // DEC indicates a Decimal alphabet
   std::ostringstream enc_oss;
   enc_oss << xml_enc;

   std::string bsn("<BallotSequenceNumber Encoding=\"DEC\">12345</BallotSequenceNumber>");

   // Generate Vote Verification Dictionary (includes Generate Vote Verification Code)
   printf("Generating Vote Verification Dictionary.\n\n");
   auto_freeing<VoteVerificationDictionary> verification_dictionary = NULL;
      result = VHTI_generate_vote_verification_dictionary(vote_verification_keys.c_str(),
         blank_ballot.c_str (), bsn.c_str(), string_len, enc_oss.str().c_str(),
         & verification_dictionary);

   if (!result)
   {
      printf("Woo hoo.  Generate Vote Verification Dictionary succeeded.\n\n");
      printf("   Vote Verification Dictionary:\n\n");
      printf("%s\n\n", static_cast<const char *> (verification_dictionary));

      auto_freeing<ConstCharStar> signed_blank_ballot = 0;
      std::string key("<RandomSeedKey>Some random string to hash for a random block.</RandomSeedKey>");
      auto_freeing<RandomState> random_state = 0;

      result  = VHTI_sign_xml (prvkey,
                               blank_ballot.c_str (),
                               &signed_blank_ballot);

      if (!result)
      {
         result = VHTI_generate_random_state(key.c_str(), &random_state);
      }
      else
      {
         printf("Uh oh.  Signing XML failed.\n\n");
         exit(1);
      }
        
      auto_freeing< SignedVotedBallot > signed_voted_ballot = 0;
      if (!result)
      {
         // Encrypt the ballot at the pollsite
         printf("Encrypt the ballot at the pollsite:\n\n");
         
         auto_freeing<RandomState> return_random_state = 0;
         result = VHTI_encrypt_ballot_pollsite (ctb.c_str(), blank_ballot.c_str(),
            bsn.c_str(), random_state, prvkey, 
            & signed_voted_ballot, &return_random_state);

         random_state = VHTI_dup(return_random_state);
      }
      else
      {
         printf("Uh oh.  Generate Random State failed.\n\n");
         exit(1);
      }

      if (!result)
      {
         printf("Woo hoo.  Ballot encryption succeeded.\n\n");
         printf("  Signed Voted Ballot:\n\n");
         printf("%s\n\n", static_cast<const char *> (signed_voted_ballot));

         // Generate Vote Receipt Data
         printf("Generating Vote Receipt Data.\n\n");
         
         // Generate Verification Codes for each BallotSequenceNumber
         auto_freeing<VoteReceiptData> vote_receipt_data = NULL;
         result = VHTI_generate_vote_receipt_data(signed_voted_ballot, vote_verification_keys.c_str(),
            blank_ballot.c_str (), bsn.c_str(), ctb.c_str(), string_len, enc_oss.str().c_str(),
            & vote_receipt_data);

         if (!result)
         {
            printf("Woo hoo.  Generate Vote Receipt Data succeeded.\n\n");
            printf("   Vote Receipt Data:\n\n");
            printf("%s\n\n", static_cast<const char *> (vote_receipt_data));
            
            // Sign Receipt
            printf("Signing Vote Receipt.\n\n");
            auto_freeing<VoteReceiptData> vote_receipt = NULL;
            result = VHTI_sign_receipt(vote_receipt_data, PollsiteSigPrvkey.c_str(), &vote_receipt);

            if (!result)
            {
               printf("Woo hoo.  Signing Vote Receipt Data succeeded.\n\n");
               printf("  Signed Receipt Data:\n\n");
               printf("%s\n\n", static_cast<const char *> (vote_receipt));
            }
            else
            {
               printf("Uh oh.  Signing Receipt Data failed.\n\n");
               exit(1);
            }
         }
         else
         {
            printf("Uh oh.  Receipt Data Generation failed.\n\n");
            exit(1);
         }
      }
      else
      {
         printf("Uh oh.  Ballot encryption failed.\n\n");
         exit(1);
      }
   }

   printf("Voting sample FINISHED EXECUTING.\n\n");
   return result;
}
