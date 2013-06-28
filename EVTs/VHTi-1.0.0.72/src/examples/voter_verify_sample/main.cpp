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

#if defined (LEAK_CHECK)
extern "C" {
#define MP_NOCPLUSPLUS 1
#include <mpatrol.h>
#include <mpatrol/tools/heapdiff.h>
}
#endif

#include "vhti/keyshare_util.h"
#include <vhti/gen_seccoeff.h>
#include <vhti/gen_broadcast.h>
#include <vhti/gen_pubkey.h>
#include <vhti/gen_secrets.h>
#include <vhti/gen_comm.h>
#include <vhti/check_comm.h>
#include <vhti/gen_blank_ballot.h>
#include "vhti/gen_bsns.h"
#include "vhti/gen_vvkey.h"
#include "vhti/gen_vote_receipt_data.h"
#include "vhti/gen_vvdict_comm.h"
#include "vhti/gen_vvdict.h"
#include "vhti/sign.h"
#include "vhti/sign_receipt.h"
#include "vhti/enc_ballot_pollsite.h"
#include "vhti/genkeys.h"
#include "vhti/random.h"
#include "vhti/support.h"
#include "vhti/types.h"
#include "vhti/auth.h"
#include "vhti/shuffle.h"
#include "vhti/check_shuffle.h"
#include "vhti/partial_decrypt.h"
#include "vhti/check_partial_decrypt.h"
#include "vhti/check_pds_and_combine.h"
#include "vhti/gen_pre_verification_results.h"
#include "vhti/gen_pv_results.h"
#include "vhti/check_vc_pds_and_combine.h"
#include "vhti/gen_dictionary_secrets.h"
#include "vhti/check_dictionary_secrets.h"
#include "vhti/combine_dictionary_secrets.h"
#include "misc/vh_cout.h"
#include "misc/xml_tree.h"
#include "misc/safe_xml_tree.h"

#include <cassert>
#include <string>
#include <sstream>
#include <fstream>
#include <iostream>

#include <sys/stat.h>
#include <io.h>

namespace {
   bool
   dump (const std::string &stuff,
         const std::string &output_file_name)
   {
      bool fOK = false;
      chmod (output_file_name.c_str (), _S_IWRITE);
      std::ofstream outfile (output_file_name.c_str ());
      if (!outfile)
         std::cerr << "Uh oh: "
                   << output_file_name
                   << ": "
                   << strerror (errno)
                   << std::endl;
      else
      {
         outfile << stuff;
         fOK = !outfile.fail ();
      }

      return fOK;
   }

   bool
   dump (VHUtil::xml_tree::node *stuff,
         const std::string &output_file_name)
   {
      std::ostringstream tmp;
      tmp << *stuff;
      return dump (tmp.str (), output_file_name);
   }
}

int
main()
{
#if defined (LEAK_CHECK)
   heapdiff hd;
   heapdiffstart (hd, HD_UNFREED | HD_FULL);
#endif
   int result = 0;
   int icount=0;

   ///////////////////////////////////////////////////////////////////////////
   //First generate the election configuration and the voting dictionary
   //commitments.
   ///////////////////////////////////////////////////////////////////////////

   // Setup: RandomState
   // This is just to generate stuff from.
   auto_freeing<RandomState> random_state = NULL;
   auto_freeing<RandomState> return_random_state = NULL;

   std::string key("<RandomSeedKey>Some random string, used to initialize the random state.</RandomSeedKey>");
   result = VHTI_generate_random_state(key.c_str(), &random_state);
   assert(! result);

   // Setup: KeyGenParameters
   printf("*******************************************************\n\n");
   printf("Creating key generation parameters.");
   char *numAuth = "1";
   char *thrAuth = "1";
   char *seed = "123";
   auto_freeing<KeyGenParameters> key_gen_parameters = 0;
   VHUtil::xml_tree xml_seed("<" SEED_PARAMETERS "/>");

   xml_seed.root ()->new_element (NUM_AUTH)       ->add_characters (numAuth);
   xml_seed.root ()->new_element (THRESHOLD)      ->add_characters (thrAuth);

   std::ostringstream seed_stream;
   seed_stream << xml_seed;
   char * in_kgp = VHTI_dup(seed_stream.str().c_str());

   result = VHTI_create_keygen_parameters(in_kgp,
                                          random_state,
                                          &key_gen_parameters,
                                          &return_random_state);

   printf("\n\nKey Generation Parameters:");
   printf("\n%s", static_cast<const char *> (key_gen_parameters));

   std::string str_kgp(key_gen_parameters);
   VHUtil::xml_tree xml_kgp(str_kgp);
   VHUtil::xml_node root_kgp = xml_kgp.root();

   // Input: Authority 
   // This is just the information to describe a single authority.  We are
   // using the assumption that the authorities responsible for voter
   // verification are the same as the ones responsible for tabulation.
   printf("\n\n*******************************************************\n\n");
   printf("Creating Authority object.");
   auto_freeing< Authority > authority = 0;
   {
      auto_freeing<GeneralPurposePrivateKey> pr = 0;
      result = VHTI_create_authority("1",
                                     key_gen_parameters, 
                                     random_state,
                                     0,
                                     &pr,
                                     &authority,
                                     &return_random_state);
   }
   assert(! result);
   printf("\n\nAuthority:");
   printf("\n%s", static_cast<const char *> (authority));
   std::string str_authority(authority);
   VHUtil::xml_tree xml_authority(str_authority);
   VHUtil::xml_node root_authority = xml_authority.root();
   std::string authID = root_authority->attribute(AUTH_FINGERPRINT);

   random_state = VHTI_dup(return_random_state);

   printf("\n\n*******************************************************\n\n");
   printf("Generating Blank Ballot.");

   // Generate the authority's secret coefficients
   auto_freeing<SecretCoefficients> secret_coefficients = 0;
   result = VHTI_generate_secret_coefficients(key_gen_parameters, authority,
      random_state, &secret_coefficients, &return_random_state);
   assert(! result);
   random_state = VHTI_dup(return_random_state);

   // Generate the authority's broadcast values
   auto_freeing<BroadcastValue> broadcast_value = 0;            
   result = VHTI_generate_broadcast(key_gen_parameters, secret_coefficients,
      random_state, &broadcast_value, &return_random_state);
   assert(! result);
   random_state = VHTI_dup(return_random_state);

   VHUtil::xml_tree xml_all_bvs("<" BROADCAST_VALUES "/>");
   VHUtil::xml_node root_all_bvs = xml_all_bvs.root();
   VHUtil::xml_tree xml_bv((char *)broadcast_value);
   root_all_bvs->add_element(xml_bv.root()->deep_copy());
   
   // Now we can generate the public key
   std::ostringstream all_bvs_stream;
   all_bvs_stream << xml_all_bvs;
   
   auto_freeing<ElectionPublicKey> public_key = 0;
   result = VHTI_generate_public_key(key_gen_parameters, all_bvs_stream.str().c_str(),
      &public_key);
   assert(! result);

   VHUtil::cout() << "ELECTION PUBLIC KEY" << std::endl;
   std::string ePublicKey(public_key);
   VHUtil::xml_tree xml_ekey(ePublicKey);
   VHUtil::xml_node root_ekey = xml_ekey.root();
   VHUtil::cout() << ePublicKey << std::endl;

   // Generate the authority's secrets
   // Since we only have one authority, the FromID is the same as the ToID
   auto_freeing<PairwiseSecret> pairwise_secret = 0;
   result = VHTI_generate_secret(key_gen_parameters, authority,
      secret_coefficients, &pairwise_secret);
   assert(! result);

   VHUtil::xml_tree xml_pss("<" PAIRWISE_SECRETS "/>");
   VHUtil::xml_node root_pss = xml_pss.root();
   VHUtil::xml_tree xml_ps((char *)pairwise_secret);
   root_pss->add_element(xml_ps.root()->deep_copy());

   std::ostringstream toid_secrets_stream;
   toid_secrets_stream << xml_pss;

   // Generate the authority's secret share and key share commitment
   auto_freeing<SecretShare> secret_share = 0;
   auto_freeing<KeyShareCommitment> keyshare_commitment = 0;
   result = VHTI_generate_commitment(key_gen_parameters, authority,
      all_bvs_stream.str().c_str(), toid_secrets_stream.str().c_str(),
      &secret_share, &keyshare_commitment);
   assert(! result);

   {
      VHUtil::xml_tree secret_shares ("<" "BunchaSecretShares" "/>");
      secret_shares.root ()->add_element (VHUtil::xml_tree (static_cast<const char *>(secret_share))
                                          .root ()
                                          ->deep_copy ());
      dump (secret_shares.root (), "../secret-shares.xml");
   }
   
   VHUtil::xml_tree xml_ksc((char *)keyshare_commitment);
   VHUtil::xml_node root_ksc = xml_ksc.root();
   
   // Check the commitment
   auto_freeing<CheckResults> check_comm_result = 0;
   result = VHTI_check_commitment(key_gen_parameters, authority,
      all_bvs_stream.str().c_str(), keyshare_commitment, &check_comm_result);
   assert(! result);

   if (!strstr(check_comm_result, CHECK_SUCCESS_TEXT))
   {
      VHUtil::cout() << "Uh oh -- the commitment didn't check: "
                     << check_comm_result
                     << std::endl;
      exit(1);
   }
   // Now we build the CryptoElectionParameters to pass to generate_blank_ballot
   VHUtil::xml_tree xml_cep("<" CRYPTO_ELECTION_PARAMETERS "/>");
   VHUtil::xml_node root_cep = xml_cep.root();

   // CryptoGroupParameters
   root_cep->add_element(root_kgp->e(CRYPTO_GROUP_PARAMETERS)->deep_copy());

   // CryptoTabulationParameters
   VHUtil::xml_tree xml_ctp("<" CRYPTO_TABULATION_PARAMETERS "/>");
   VHUtil::xml_node root_ctp = xml_ctp.root();
   root_ctp->add_element(root_ekey->deep_copy());
   root_ctp->add_element(root_kgp->e(NUM_AUTH)->deep_copy());
   root_ctp->add_element(root_kgp->e(THRESHOLD)->deep_copy());
   root_ctp->add_element(root_ksc->deep_copy());
   root_cep->add_element(root_ctp->deep_copy());

   std::ostringstream oss_cep;
   oss_cep << xml_cep;

   // Make xml for ElectionID, PrecinctID and BallotQuestions
   std::string eid("<ElectionID>21740</ElectionID>");
   std::string pid("<PrecinctID>99</PrecinctID>");
   
   std::string ballot_skeleton(
      "<BallotSkeleton>"
      "<ElectionID>21740</ElectionID>"
      "<PrecinctID>99</PrecinctID>"
      "<QuestionSkeleton>"
      "<AnswerSkeleton/>"
      "<AnswerSkeleton/>"
      "<AnswerSkeleton/>"
      "</QuestionSkeleton>"
      "<QuestionSkeleton>"
      "<AnswerSkeleton/>"
      "<AnswerSkeleton/>"
      "<AnswerSkeleton/>"
      "</QuestionSkeleton>"
      "</BallotSkeleton>");
   std::string encoding("<AlphabetEncoding>DEC</AlphabetEncoding>");

   std::string blank_ballot;
   {
      auto_freeing< BlankBallot > bb = 0;
      result = VHTI_generate_blank_ballot(ballot_skeleton.c_str(), oss_cep.str().c_str(),
                                          encoding.c_str(), &bb);
      assert(! result);
      blank_ballot = bb;
   }
   printf("\n\nBlank Ballot:");
   printf("\n%s", blank_ballot.c_str ());

   // *********************
   // Input: VoteVerificationKey - generate one per trustee
   auto_freeing<RandomState> vvk_random_state = NULL;
   auto_freeing<VoteVerificationKey> vote_verification_key = NULL;
   {
      std::string secret_vvk_passphrase("<RandomSeedKey>Some other random string, used to "
         "initialize the VoteVerificationKey.</RandomSeedKey>");
      
      result = VHTI_generate_random_state(secret_vvk_passphrase.c_str(), &vvk_random_state);
      assert(! result);
   }
   printf("\n\n*******************************************************\n\n");
   printf("Generating Vote Verification Key.");
   auto_freeing< RandomState > return_vvk_random_state = 0;
   result = VHTI_generate_vvk(vvk_random_state, &vote_verification_key, &return_vvk_random_state);
   assert(! result);
   printf("\n\nVote Verification Key:");
   printf("\n%s", static_cast<const char *> (vote_verification_key));

   // The VoteVerificationKeys is a list of all the vote verification key
   // objects.
   std::string vote_verification_keys;
   {
      VHUtil::xml_tree xml_vvks ("<" VOTE_VERIFICATION_KEYS "/>");
      xml_vvks.root ()->add_element (VHUtil::xml_tree (static_cast<const char *>(vote_verification_key)).root ()->deep_copy ());
      std::ostringstream tmp;
      tmp << xml_vvks;
      vote_verification_keys = tmp.str ();
      dump (vote_verification_keys, "../vvks.xml");
   }

   // Input: BallotSequenceNumbers
   auto_freeing<BallotSequenceNumbers> auth_bsn = NULL;
   auto_freeing<BallotSequenceNumbers> prov_bsn = NULL;
   int num_auth_voters = 3;
   int num_prov_voters = 2;

   printf("\n\n*******************************************************\n\n");
   printf("Generating Ballot Sequence Numbers.");
   result = VHTI_generate_bsns(eid.c_str(), pid.c_str(), num_auth_voters, num_prov_voters,
      random_state, &auth_bsn, &prov_bsn, &return_random_state);
   assert(! result);
   std::string str_auth_bsn(auth_bsn);
   VHUtil::xml_tree xml_auth_bsn(str_auth_bsn);
   VHUtil::xml_node root_auth_bsn = xml_auth_bsn.root();
   printf("\n\nAuthorized Ballot Sequence Numbers:");
   printf("\n%s", static_cast<const char *> (auth_bsn));
   printf("\n\nProvisional Ballot Sequence Numbers:");
   printf("\n%s", static_cast<const char *> (prov_bsn));

   // Input: GeneralPurposePrivateKey
   auto_freeing<GeneralPurposePrivateKey > TSigPrvkey = 0;
   auto_freeing<GeneralPurposePublicKey > TSigPubkey = 0;
   std::string Tio("<IdentInfo>your name</IdentInfo>");
   result = VHTI_generate_keys(Tio.c_str(), &TSigPrvkey, &TSigPubkey);
   assert(!result);

   // Output: TrusteeDictionaryCommitments
   // These should be published for the world to see.
   printf("\n\n*******************************************************\n\n");
   printf("Generating Trustee Dictionary commitments.");
   auto_freeing<TrusteeDictionaryCommitments> trustee_dict_comm = NULL;
   result = VHTI_generate_vvdict_commits (authority, TSigPrvkey,
         vote_verification_key, blank_ballot.c_str (), auth_bsn, & trustee_dict_comm);
   assert(! result);

   printf("\n\nTrustee Dictionary commitments:");
   printf("\n%s", static_cast<const char *> (trustee_dict_comm));

   // Input: Key.
   // This will be used to sign the blank ballot with.  Typically this
   // would be a closely held secret owned by the election owner, or
   // whoever is administering the election.
   
   // Generate DSA key pair
   printf("\n\n*******************************************************\n\n");
   printf("Generating Pollsite Signing Key.");
   auto_freeing<GeneralPurposePrivateKey > PollsiteSigPrvkey = 0;
   auto_freeing<GeneralPurposePublicKey > PollsiteSigPubkey = 0;
   std::string io("<IdentInfo>your name</IdentInfo>");
   result = VHTI_generate_keys(io.c_str(), &PollsiteSigPrvkey, &PollsiteSigPubkey);
   assert(!result);

   dump (static_cast<const char *>(PollsiteSigPubkey), "../ballot-signing-pubkey.xml");
   dump (static_cast<const char *>(PollsiteSigPrvkey), "../ballot-signing-prvkey.xml");
   
   printf("\n\nPollsite Signing Key:");
   printf("\n%s", static_cast<const char *> (PollsiteSigPrvkey));

   // Sign the blank ballot with the private key
   printf("\n\n*******************************************************\n\n");
   printf("Signing Blank Ballot.");

   auto_freeing<ConstCharStar > signed_blank_ballot = 0;
   result = VHTI_sign_xml (PollsiteSigPrvkey,
                           blank_ballot.c_str (),
                           &signed_blank_ballot);
   assert (!result);

   // Move the elements to where they belong.

   dump (blank_ballot, "../bb.xml");
   dump (static_cast<const char *>(signed_blank_ballot), "../sbb.xml");

   printf("\n\nSigned Blank Ballot:");
   printf("\n%s", signed_blank_ballot);

   ///////////////////////////////////////////////////////////////////////////
   // Ok, now we have a signed blank ballot.  This is allows the voter to
   // know that the ballot he is looking at is a real one.  With this, we
   // are ready for voting to happen.
   ///////////////////////////////////////////////////////////////////////////

   // Input: ClearTextBallot.  
   // This is generated by the voting client in response to the voter
   // having made (and "confirmed") his selections.
   std::string clear_text_ballots("<ClearTextBallots>"
      "<ClearTextBallot>"
      "<AnswerReference>A2</AnswerReference>"
      "<AnswerReference>A3</AnswerReference>"
      "</ClearTextBallot>"
      "<ClearTextBallot>"
      "<AnswerReference>A1</AnswerReference>"
      "<AnswerReference>A4</AnswerReference>"
      "</ClearTextBallot>"
      "<ClearTextBallot>"
      "<AnswerReference>A0</AnswerReference>"
      "<AnswerReference>A5</AnswerReference>"
      "</ClearTextBallot>"
      "</ClearTextBallots>");

   VHUtil::xml_tree xml_ctbs(clear_text_ballots);
   VHUtil::xml_node root_ctbs = xml_ctbs.root();

   // Input: RandomState (voter)
   // A random state for the voting to happen from.  In reality, what might
   // be better is to get a few bits of entropy (well, as many as we really
   // can) and add them to the previous voter's random state to make the
   // next voter's random state.  That will make the quality of the
   // randomness (and subsequently, encryption) much better.  The boot-up
   // process should include some behaviour that generates enough entropy
   // to initialize the first block.
   std::string voter_keys("<RandomSeedKeys>"
      "<RandomSeedKey>Some random string to make a random block voter 1 to use.</RandomSeedKey>"
      "<RandomSeedKey>Some random string to make a random block voter 2 to use.</RandomSeedKey>"
      "<RandomSeedKey>Some random string to make a random block voter 3 to use.</RandomSeedKey>"
      "</RandomSeedKeys>");

   VHUtil::xml_tree xml_keys(voter_keys);
   VHUtil::xml_node root_keys = xml_keys.root();

   VHUtil::xml_tree xml_svbs("<" SIGNED_VOTED_BALLOTS "/>");
   VHUtil::xml_tree xml_voter_roll ("<" VOTER_ROLL "/>");

   auto_freeing<SignedVotedBallot> signed_voted_ballot = 0;
   printf("\n\n*******************************************************\n\n");
   
   for (icount=0; icount<num_auth_voters; icount++)
   {
      VHUtil::xml_node current_bsn = root_auth_bsn->e(icount);
      std::ostringstream oss_bsn;
      oss_bsn << *current_bsn;
      printf("DATA FOR BALLOT SEQUENCE NUMBER %s:", oss_bsn.str().c_str());

      // Input: BallotSequenceNumber
      // Generate Verification Dictionary for each BallotSequenceNumber
      int string_len = 32;
      VHUtil::xml_tree xml_enc("<" ALPHABET_ENCODING "/>");
      VHUtil::xml_node root_enc = xml_enc.root();
      root_enc->add_characters("DEC");  // DEC indicates a Decimal alphabet
      std::ostringstream enc_oss;
      enc_oss << xml_enc;

      printf("\n\n   Vote Verification Dictionary:");
      auto_freeing<VoteVerificationDictionary> verification_dictionary = NULL;
      result = VHTI_generate_vote_verification_dictionary(vote_verification_keys.c_str(),
         blank_ballot.c_str (), oss_bsn.str().c_str(), string_len, enc_oss.str().c_str(),
         & verification_dictionary);
      assert(! result);
      
      printf("\n\n%s", static_cast<const char *> (verification_dictionary));

      if (icount < num_auth_voters-1) // These guys actually use the bsn to vote
      {
         VHUtil::xml_node current_ctb = root_ctbs->e(icount);
         VHUtil::xml_node current_key = root_keys->e(icount);
         std::ostringstream oss_ctb;
         oss_ctb << *current_ctb;
         std::ostringstream oss_key;
         oss_key << *current_key;
         
         auto_freeing<RandomState> voters_random_state = 0;
         result = VHTI_generate_random_state(oss_key.str().c_str(), &voters_random_state);
         assert(!result);
         
         printf("\n\n   Voter's Key and Random Bits for Ballot Encryption:");
         printf("\n\n%s", static_cast<const char *> (voters_random_state));
         
         // Output: SignedVotedBallot
         // Note: This should be signed with a key that is loaded
         // on the vote client at some point and can be used to
         // authenticate where the SignedVotedBallot came from.
         
         auto_freeing<RandomState> return_voters_random_state = 0;
         result = VHTI_encrypt_ballot_pollsite (oss_ctb.str().c_str(), blank_ballot.c_str (),
            oss_bsn.str().c_str(), voters_random_state, PollsiteSigPrvkey, 
            & signed_voted_ballot, &return_voters_random_state);
         assert(! result);
         
         xml_voter_roll.root ()
            ->new_element (CERTIFICATE)
            ->add_element (VHUtil::xml_tree (static_cast<const char *>(PollsiteSigPubkey))
            .root ()
            ->deep_copy ());
         
         printf("\n\n   Signed Voted Ballot:");
         printf("\n\n%s", static_cast<const char *> (signed_voted_ballot));
         
         std::string str_svb(signed_voted_ballot);
         VHUtil::xml_tree xml_svb(str_svb);
         VHUtil::xml_node root_svb = xml_svb.root();
         xml_svbs.root ()->add_element(root_svb->deep_copy());
         
         // Output: VoteReceiptData
         // Now, we need to present the receipt to the voter.  Once the voter is
         // satisfied with this receipt, we will encrypt (and sign) the ballot,
         // and present the voter with a VoteReceipt.  But first the
         // VoteReceiptData.
         
         // Input: BallotSequenceNumber
         // Generate Verification Codes for each BallotSequenceNumber
         printf("\n\n   Vote Receipt Data:");
         auto_freeing<VoteReceiptData> vote_receipt_data = NULL;
         result = VHTI_generate_vote_receipt_data(signed_voted_ballot, vote_verification_keys.c_str(),
            blank_ballot.c_str (), oss_bsn.str().c_str(), oss_ctb.str().c_str(), string_len, enc_oss.str().c_str(),
            & vote_receipt_data);
         assert(! result);
         
         printf("\n\n%s", static_cast<const char *> (vote_receipt_data));
         
         // Output: VoteReceipt
         // This is the last thing presented to the voter.
         // Many voters might not be able to check that the signature is valid right away,
         // unless a publicly available means is made available.
         printf("\n\n   Signed Vote Receipt:");
         auto_freeing<VoteReceiptData> vote_receipt = NULL;
         result = VHTI_sign_receipt(vote_receipt_data, PollsiteSigPrvkey, &vote_receipt);
         assert(! result);
         
         printf("\n\n%s", static_cast<const char *> (vote_receipt));
      }
      printf("\n\n*******************************************************\n\n");
   }

   std::ostringstream oss_svbs;
   oss_svbs << xml_svbs;
   std::ostringstream oss_voter_roll;
   dump (oss_svbs.str (), "../svbs.xml");

   {
      oss_voter_roll << xml_voter_roll;
      dump (oss_voter_roll.str (), "../voter-roll.xml");
   }

   // <- authenticate <- svbs, voter roll, blank ballot
   std::string raw_ballot_box;
   {
      std::string sbb(signed_blank_ballot);
      std::string ps_pubkey(PollsiteSigPubkey);
      VHUtil::safe_xml_tree xml_sbb (sbb, BLANK_BALLOT, ps_pubkey);
      auto_freeing<RawBallotBox> tmp = 0;
      std::ostringstream sbb_stream;
      sbb_stream << *(xml_sbb.root ());
      result = VHTI_authenticate (oss_svbs.str().c_str (),
         oss_voter_roll.str().c_str(),
         sbb_stream.str ().c_str (),
         &tmp);

      if (!result)
         raw_ballot_box = std::string (tmp);
   }
   
   auto_freeing<RawBallotBox> raw_ballot_box_after = 0;
   auto_freeing<ShuffleValidityProof> shuffle_validity_proof = 0;
   
   if (!result)
   {
      // Shuffle ballots
      printf("Shuffling Ballots");
      result = VHTI_shuffle(raw_ballot_box.c_str(), random_state,
         signed_blank_ballot,
         PollsiteSigPubkey,
         &raw_ballot_box_after, &return_random_state,
         &shuffle_validity_proof);
      random_state = VHTI_dup(return_random_state);
      
      if (!result)
      {
         printf("    \n\nSuccess!");
         printf("\n\nThe Shuffle Validity Proof is as follows:");
         printf("\n\n%s", shuffle_validity_proof);
      }
      else
      {
         printf("Uh oh, the shuffle proof code failed.\n\n");
         exit(1);
      }
   }
   
   if (!result)
   {
      // Check shuffle validity proof
      printf("\n\nChecking the Shuffle");
      auto_freeing<CheckResults> check_shuffle_result = 0;
      result = VHTI_check_shuffle(raw_ballot_box.c_str(), raw_ballot_box_after, signed_blank_ballot,
         PollsiteSigPubkey,
         shuffle_validity_proof, &check_shuffle_result);
      
      if ((!result)
         &&
         strstr (check_shuffle_result, CHECK_SUCCESS_TEXT))
      {
         printf("    \n\nSuccess!");
         printf("\n\n%s", check_shuffle_result);
         printf("\n\nThe shuffle validity proof checking is complete.");
      }
      else
      {
         printf("\n\nUh oh, the shuffle proof checking code failed.\n\n");
         exit(1);
      }
   }
   printf("\n\n*******************************************************\n\n");



   // Build a CommittedAuthority
   VHUtil::xml_tree xml_auth_set ("<" COMMITTED_AUTHORITY_SET "/>");
   VHUtil::xml_tree::node *auth_node = xml_auth_set.root ()->new_element (COMMITTED_AUTHORITY);
   auth_node->add_element(root_authority->deep_copy());
   auth_node->add_element(root_ksc->deep_copy());
   
   dump (xml_auth_set.root (), "../committed-authority-set.xml");
   
   std::ostringstream oss_comm_auth;
   oss_comm_auth << *(xml_auth_set.root ()->e (0));

   // Make a PDBB container to use in combine decrypts function
   VHUtil::xml_tree xml_pdbb("<PartiallyDecryptedBallotBox/>");
   VHUtil::xml_node root_pdbb = xml_pdbb.root();
   
   VHUtil::xml_tree xml_auth_pds("<AuthorityPartialDecrypts/>");
   VHUtil::xml_node root_auth_pds = xml_auth_pds.root();

   // Put the Shuffled RBB in the PartiallyDecryptedBallotBox
   std::string str_rbb_after(raw_ballot_box_after);
   VHUtil::xml_tree xml_rbb_after(str_rbb_after);
   VHUtil::xml_node root_rbb_after = xml_rbb_after.root();
   root_pdbb->add_element(root_rbb_after->deep_copy());
   
   if (!result)
   {
      printf("\n\nPartial decryption of raw ballot box by authority %s.", authID.c_str());
      
      auto_freeing<AuthorityPartialDecrypt> auth_partial_decrypt = 0;
      result = VHTI_partial_decrypt(raw_ballot_box_after, signed_blank_ballot,
         PollsiteSigPubkey,
         oss_comm_auth.str().c_str(),
         secret_share, random_state,
         &auth_partial_decrypt, &return_random_state);
      random_state = VHTI_dup(return_random_state);
      
      if (!result)
      {
         printf("\n\n    Success!");
         printf("\n\nThe Authority Partial Decrypt:");
         printf("%s\n\n", auth_partial_decrypt);

         VHUtil::xml_tree xml_auth_pd((char *)auth_partial_decrypt);
         VHUtil::xml_node root_auth_pd = xml_auth_pd.root();
         std::ostringstream auth_pd_stream;
         auth_pd_stream << xml_auth_pd;
         
         root_auth_pds->add_element(root_auth_pd->deep_copy());
         
         if (!result)
         {
            // Check the Partial Decrypt
            printf("\n\nChecking partial decrypt.");
            auto_freeing<Results> check_partial_decrypt_result = 0;
            result = VHTI_check_partial_decrypt(raw_ballot_box_after,
               auth_partial_decrypt,
               signed_blank_ballot, PollsiteSigPubkey,
               &check_partial_decrypt_result);
            
            if (!result)
            {
               printf("\n\n    Check of partial decrypt SUCCEEDED !");
               printf("\n\n%s", check_partial_decrypt_result);
            }
            else
            {
               printf("\n\n    Check of partial decrypt FAILED !\n");
               exit(1);
            }
         }
      }
      else
      {
         printf("\n\n    Partial decryption by authority %s failed.\n", authID.c_str());
         exit(1);
      }
   }
   
   if (!result)
   {
      // Put the AuthorityPartialDecrypts into the PartiallyDecryptedBallotBox
      root_pdbb->add_element(root_auth_pds->deep_copy());
      
      printf("\n\nPartial decryption and checking by all authorities is successfully complete.");
      printf("\n\nThe AuthorityPartialDecrypts are as follows:");
      std::ostringstream oss;
      oss << xml_auth_pds;
      printf("\n\n%s", oss.str().c_str());
   }
   else
   {
      printf("\n\nPartial decryption and checking has not been successfully completed.");
      exit(1);
   }
   
   if (!result)
   {
      // Check partial decrypts and combine
      auto_freeing<ClearTextBallots> clear_text_ballots = 0;
      auto_freeing<Results> combine_partial_decrypt_result = 0;
      
      std::ostringstream pdbb_stream;
      pdbb_stream << xml_pdbb;
      
      VHUtil::cout() << "xml_pdbb is " << xml_pdbb << std::endl;
      
      printf("\n\nChecking each partial decrypt, then combining them.");
      
      result = VHTI_check_partial_decrypts_and_combine
         (signed_blank_ballot, PollsiteSigPubkey,
         pdbb_stream.str().c_str(),
         &clear_text_ballots, &combine_partial_decrypt_result);
      
      if (!result
         &&
         strstr(combine_partial_decrypt_result, CHECK_SUCCESS_TEXT))
      {
         printf("\n\n    Success!");
         printf("\n\nCombined decryption by all authorities is complete.");
         printf("\n\n%s", combine_partial_decrypt_result);
         printf("\n\nThe Clear Text Ballots are as follows:");
         printf("\n\n%s", clear_text_ballots);
      }
      else
      {
         printf("\n\nFailure to complete combined decryption successfully.\n\n");
         exit(1);
      }
   }

   printf("\n\n*******************************************************\n\n");
   
   if (!result)
   {
      VHUtil::xml_tree xml_pvc_boxes("<" PRE_VERIFICATION_CODE_BOXES "/>");
      VHUtil::xml_node root_pvc_boxes = xml_pvc_boxes.root();
      
      // Generate PreVerificationCodes
      auto_freeing < PreVerificationCodeBox > pre_vcode_box = 0;
      result = VHTI_generate_pre_verification_results
         (vote_verification_key, oss_svbs.str().c_str(),
          signed_blank_ballot, PollsiteSigPubkey, &pre_vcode_box);
      
      if (!result)
      {
         std::string str_pvc(pre_vcode_box);
         VHUtil::xml_tree xml_pvc(str_pvc);
         VHUtil::xml_node root_pvc = xml_pvc.root();
      
         // Add these PreVerificationCodes to collection from all trustees
         root_pvc_boxes->add_element(root_pvc->deep_copy());
      
         VHUtil::xml_tree xml_auth_pds_for_vcodes("<" AUTHORITY_PARTIAL_DECRYPTS "/>");
         VHUtil::xml_node root_auth_pds_for_vcodes = xml_auth_pds_for_vcodes.root();
      
         std::ostringstream oss_pvc_boxes;
         oss_pvc_boxes << xml_pvc_boxes;

         if (!result)
         {
            // Each authority takes all of the verification codes and multiplies them
            // together, then does a partial decrypt
            printf("Partial decryption of Verification Codes by authority 1.\n");
         
            auto_freeing< AuthorityPartialDecrypt > auth_partial_decrypt_of_verifications = 0;
            result = VHTI_generate_partial_verification_results
               (oss_pvc_boxes.str().c_str(),
                signed_blank_ballot, PollsiteSigPubkey, oss_comm_auth.str().c_str(), secret_share, random_state,
                &auth_partial_decrypt_of_verifications, &return_random_state);

            if (!result)
            {
               random_state = VHTI_dup(return_random_state);
               printf("    Success!");
               VHUtil::xml_tree xml_auth_pd((char *)auth_partial_decrypt_of_verifications);
               VHUtil::xml_node root_auth_pd = xml_auth_pd.root();
               std::ostringstream auth_pd_stream;
               auth_pd_stream << xml_auth_pd;
            
               root_auth_pds_for_vcodes->add_element(root_auth_pd->deep_copy());
            }
            else
            {
               printf("    Partial decryption of Verification Codes by authority 1 failed.\n");
               exit(1);
            }
         }

         std::ostringstream oss_auth_pds_vc;
         oss_auth_pds_vc << xml_auth_pds_for_vcodes;

         if (!result)
         {
            // Check partial decrypts and combine
            auto_freeing<VoteVerificationStatements> verification_statements = 0;
            auto_freeing<Results> combine_partial_decrypt_result = 0;

            int string_len = 32;
            VHUtil::xml_tree xml_enc("<" ALPHABET_ENCODING "/>");
            VHUtil::xml_node root_enc = xml_enc.root();
            root_enc->add_characters("DEC");  // DEC indicates a Decimal alphabet
            std::ostringstream enc_oss;
            enc_oss << xml_enc;

            printf("\n\nChecking each partial decrypt of verification codes, then combining them.\n");
            result = VHTI_check_vcode_partial_decrypts_and_combine
               (oss_pvc_boxes.str().c_str(),
                oss_auth_pds_vc.str().c_str(), oss_svbs.str().c_str(), signed_blank_ballot,
                PollsiteSigPubkey,
                string_len, enc_oss.str().c_str(),
                &verification_statements, &combine_partial_decrypt_result);
         
            if (!result
                &&
                strstr(combine_partial_decrypt_result, CHECK_SUCCESS_TEXT))
            {
               printf("    Success!\n");
               printf("Combined decryption of Verification Statements by all authorities is complete.\n\n");
               printf("The Verification Statements are as follows:\n\n");
               printf("%s", static_cast<const char *> (verification_statements));
               std::string str_ctb(verification_statements);
            }
            else
            {
               printf("Failure to complete combined decryption successfully.\n\n");
               exit(1);
            }
         }
      }
   }

   if (!result)
   {
      // An xml tree to hold the secrets from each trustee
      VHUtil::xml_tree xml_tds_box("<" TRUSTEE_REVEALED_DICTIONARY_SECRETS_BOX "/>");
      VHUtil::xml_node root_tds_box = xml_tds_box.root();

      printf("\n\n*******************************************************\n\n");
      printf("\n\nGenerating Dictionary Secrets for each unvoted Ballot Sequence Number.\n");
      auto_freeing< TrusteeRevealedDictionarySecrets > dictionary_secrets = 0;
      result = VHTI_generate_dictionary_secrets (oss_svbs.str().c_str(),authority,
         TSigPrvkey, vote_verification_key, blank_ballot.c_str (), auth_bsn,
         & dictionary_secrets);
      assert(! result);

      // Add these secrets to the box
      std::string str_secrets(dictionary_secrets);
      VHUtil::xml_tree xml_secrets(str_secrets);
      VHUtil::xml_node root_secrets = xml_secrets.root();
      root_tds_box->add_element(root_secrets->deep_copy());

      if (!result)
      {
         printf("    Success!\n");
         printf("The Dictionary Secrets are as follows:\n\n");
         printf("%s", static_cast<const char *> (dictionary_secrets));

         printf("\n\nChecking Dictionary Secrets.\n");
         auto_freeing< CheckResults > check_dictionary_secrets_results = 0;
         result = VHTI_check_dictionary_secrets(dictionary_secrets, trustee_dict_comm,
            TSigPubkey, blank_ballot.c_str(), & check_dictionary_secrets_results);
         assert(! result);

         if (!result)
         {
            printf("    Success!\n");
            printf("The Dictionary Secrets Check Results are as follows:\n\n");
            printf("%s", static_cast<const char *> (check_dictionary_secrets_results));
            
            printf("\n\n*******************************************************\n\n");
            printf("\n\nCombining Dictionary Secrets.\n");
            auto_freeing< VoteVerificationDictionaries > verification_dicts4unvoted_bsns = 0;
            
            std::ostringstream oss_tdsb;
            oss_tdsb << xml_tds_box;
            
            int string_len = 32;
            VHUtil::xml_tree xml_enc("<" ALPHABET_ENCODING "/>");
            VHUtil::xml_node root_enc = xml_enc.root();
            root_enc->add_characters("DEC");  // DEC indicates a Decimal alphabet
            std::ostringstream enc_oss;
            enc_oss << xml_enc;
            
            result = VHTI_combine_dictionary_secrets (oss_tdsb.str().c_str(), blank_ballot.c_str(),
               string_len, enc_oss.str().c_str(), &verification_dicts4unvoted_bsns);

            if (!result)
            {
               printf("    Success!\n");
               printf("The Verification Dictionaries for the un-voted BSNs are as follows:\n\n");
               printf("%s", static_cast<const char *> (verification_dicts4unvoted_bsns));
            }
            else
            {
               printf("    Uh oh, VHTI_combine_dictionary_secrets failed.\n");
               exit(1);
            }
         }
         else
         {
            printf("    Uh oh, VHTI_check_dictionary_secrets failed.\n");
            exit(1);
         }

      }
      else
      {
         printf("    Uh oh, VHTI_generate_dictionary_secrets failed.\n");
         exit(1);
      }
   }

 #if defined (LEAK_CHECK)
   heapdiffend(hd);
#endif
   printf("\n\nPollsite SVC sample %s.\n",
          (0 == result
           ? "FINISHED EXECUTING"
           : "FAILED"));
   return result;
}

