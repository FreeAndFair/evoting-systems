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

#include "vhti/types.h"
#include "support_test/test-data.h"
#include <test_misc/test-misc.h>

// These are all well-formed, but invalid.
const char *const invalid_svb = "<" VOTER_ROLL " />";
const char *const invalid_svbs = "<" VOTER_ROLL " />";
const char *const invalid_vr  = "<" BLANK_BALLOT "> Hey you!!</" BLANK_BALLOT ">";
const char *const invalid_bb  = "<" VOTER_ROLL " />";
const char *const invalid_sbb  = "<" VOTER_ROLL " />";
const char *const invalid_rbb = "<" VOTER_ROLL " />";
const char *const invalid_rbb_before = "<" VOTER_ROLL " />";
const char *const invalid_rbb_after = "<" VOTER_ROLL " />";
const char *const invalid_sv_proof = "<" VOTER_ROLL " />";
const char *const invalid_pd_ballot_box = "<" VOTER_ROLL " />";
const char *const invalid_auth_pd = "<" VOTER_ROLL " />";
const char *const invalid_auth_pds = "<" VOTER_ROLL " />";
const char *const invalid_auth_pds_4vc = "<" VOTER_ROLL " />";
const char *const invalid_committed_authority = "<" VOTER_ROLL " />";
const char *const invalid_secret_share = "<" AUTHORITY " />";
const char *const invalid_random_state = "<" AUTHORITY " />";
const char *const invalid_modular_int = "<" KEY_GEN_PARAMETERS " />";
const char *const invalid_vkey = "<" VOTER_ROLL" />";
const char *const invalid_pvc_boxes = "<" VOTER_ROLL" />";
const char *const invalid_encoding = "<" VOTER_ROLL" />";
const char *const invalid_bsns = "<" VOTER_ROLL" />";
const char *const invalid_prvkey = "<" VOTER_ROLL" />";
const char *const invalid_pubkey = "<" VOTER_ROLL" />";
const char *const invalid_authority = "<" VOTER_ROLL" />";
const char *const invalid_trustee_dict_secrets = "<" VOTER_ROLL" />";
const char *const invalid_trustee_dict_comm = "<" VOTER_ROLL" />";
const char *const invalid_trustee_dict_secrets_box = "<" VOTER_ROLL" />";
const char *const invalid_trustee_pubkey = "<" VOTER_ROLL" />";

const char * valid_svb;

const char * valid_svbs;

const char * valid_vr;

const char * valid_bb;

const char * valid_rbb;

const char * valid_rbb_before;

const char * valid_rbb_after;

const char * valid_authority;

const char * valid_auth_pd;

const char * valid_auth_pds;

const char * valid_pd_ballot_box;

const char * valid_sbb;

const char * valid_prvkey;

const char * valid_pubkey;

const char * valid_committed_authority;

const char *valid_trustee_dict_secrets;

const char *valid_trustee_dict_secrets_box;

const char *valid_trustee_dict_comm;

const char * const valid_bsns = 
"<BallotSequenceNumbers>"
"<BallotSequenceNumber Encoding=\"DEC\">401032216162872801024413</BallotSequenceNumber>"
"<BallotSequenceNumber Encoding=\"DEC\">401032216162871826914187</BallotSequenceNumber>"
"<BallotSequenceNumber Encoding=\"DEC\">401032216162871889904076</BallotSequenceNumber>"
"</BallotSequenceNumbers>";

const char *const valid_secret_share =
"<SecretShare Encoding = \"DEC\">"
"35"
"</SecretShare>";

const char *const valid_random_state =
"<RandomState SourceType=\"PSEUDO FROM HASH\">"
"<RandomSeedKey>"
"Some kind of random data to hash"
"</RandomSeedKey>"
"<RandomBlock Encoding=\"DEC\">"
"1080159859926833460887638203863366617559462040602"
"</RandomBlock>"
"</RandomState>";

const char *const valid_modular_int =
"<ModularInt>"
"1"
"</ModularInt>";

const char * valid_sv_proof;

const char *const valid_vkey =
"<VoteVerificationKey>This here is my special key</VoteVerificationKey>";

const char * valid_pvc_boxes;

const char *const valid_encoding =
"<AlphabetEncoding>DEC</AlphabetEncoding>";

const char * valid_auth_pds_4vc;

const char * valid_trustee_pubkey;

const char *const valid_secret_shuffle_values_4b1_collsion =
"<ShuffleSecretValues>"
"<Permutation Size=\"3\">3 2 1 </Permutation>"
"<beta_values>"
"<beta Encoding=\"DEC\">477609018666059724193221366801301331399696434667</beta>"
"<beta Encoding=\"DEC\">951607981114356796084338902790512969896575114448</beta>"
"<beta Encoding=\"DEC\">804007126615105470649565060945141930842563290489</beta>"
"</beta_values>"
"<U_Values>"
"<U_Value Encoding=\"DEC\">17</U_Value>"
"<U_Value Encoding=\"DEC\">7</U_Value>"
"<U_Value Encoding=\"DEC\">25</U_Value>"
"</U_Values>"
"<W_Values>"
"<W_Value Encoding=\"DEC\">279376896430479318453762842756595393067375114166</W_Value>"
"<W_Value Encoding=\"DEC\">1120005161247525344880843443098252241620004305245</W_Value>"
"<W_Value Encoding=\"DEC\">742460865934874843577009434980335867698733289048</W_Value>"
"</W_Values>"
"<A_Values>"
"<A_Value Encoding=\"DEC\">968534025699637195314946653750098577846621472093</A_Value>"
"<A_Value Encoding=\"DEC\">494955077090081080144511943759312442230328565886</A_Value>"
"<A_Value Encoding=\"DEC\">584993699638656749118500627818073005227664016532</A_Value>"
"</A_Values>"
"<gamma Encoding=\"DEC\">482033684002464715773201605064979970137722546534</gamma>"
"<nuu Encoding=\"DEC\">17903907762269923522362103429097846827216724249</nuu>"
"<tau_0 Encoding=\"DEC\">203997733934887710638541712371271015964652564562</tau_0>"
"<tau_1 Encoding=\"DEC\">306498878352083064165168696361779147057216662544</tau_1>"
"</ShuffleSecretValues>";

const char *const valid_secret_shuffle_values_4b2_collsion =
"<ShuffleSecretValues>"
"<Permutation Size=\"3\">3 2 1 </Permutation>"
"<beta_values>"
"<beta Encoding=\"DEC\">477609018666059724193221366801301331399696434667</beta>"
"<beta Encoding=\"DEC\">951607981114356796084338902790512969896575114448</beta>"
"<beta Encoding=\"DEC\">804007126615105470649565060945141930842563290489</beta>"
"</beta_values>"
"<U_Values>"
"<U_Value Encoding=\"DEC\">16</U_Value>"
"<U_Value Encoding=\"DEC\">6</U_Value>"
"<U_Value Encoding=\"DEC\">24</U_Value>"
"</U_Values>"
"<W_Values>"
"<W_Value Encoding=\"DEC\">279376896430479318453762842756595393067375114166</W_Value>"
"<W_Value Encoding=\"DEC\">1120005161247525344880843443098252241620004305245</W_Value>"
"<W_Value Encoding=\"DEC\">742460865934874843577009434980335867698733289048</W_Value>"
"</W_Values>"
"<A_Values>"
"<A_Value Encoding=\"DEC\">9</A_Value>"
"<A_Value Encoding=\"DEC\">9</A_Value>"
"<A_Value Encoding=\"DEC\">5</A_Value>"
"</A_Values>"
"<gamma Encoding=\"DEC\">482033684002464715773201605064979970137722546534</gamma>"
"<nuu Encoding=\"DEC\">17903907762269923522362103429097846827216724249</nuu>"
"<tau_0 Encoding=\"DEC\">203997733934887710638541712371271015964652564562</tau_0>"
"<tau_1 Encoding=\"DEC\">306498878352083064165168696361779147057216662544</tau_1>"
"</ShuffleSecretValues>";

const char *const valid_secret_shuffle_values_4r_collsion =
"<ShuffleSecretValues>"
"<Permutation Size=\"3\">3 2 1 </Permutation>"
"<beta_values>"
"<beta Encoding=\"DEC\">477609018666059724193221366801301331399696434667</beta>"
"<beta Encoding=\"DEC\">951607981114356796084338902790512969896575114448</beta>"
"<beta Encoding=\"DEC\">804007126615105470649565060945141930842563290489</beta>"
"</beta_values>"
"<U_Values>"
"<U_Value Encoding=\"DEC\">7</U_Value>"
"<U_Value Encoding=\"DEC\">12</U_Value>"
"<U_Value Encoding=\"DEC\">5</U_Value>"
"</U_Values>"
"<W_Values>"
"<W_Value Encoding=\"DEC\">279376896430479318453762842756595393067375114166</W_Value>"
"<W_Value Encoding=\"DEC\">1120005161247525344880843443098252241620004305245</W_Value>"
"<W_Value Encoding=\"DEC\">742460865934874843577009434980335867698733289048</W_Value>"
"</W_Values>"
"<A_Values>"
"<A_Value Encoding=\"DEC\">2</A_Value>"
"<A_Value Encoding=\"DEC\">34</A_Value>"
"<A_Value Encoding=\"DEC\">12</A_Value>"
"</A_Values>"
"<gamma Encoding=\"DEC\">482033684002464715773201605064979970137722546534</gamma>"
"<nuu Encoding=\"DEC\">17903907762269923522362103429097846827216724249</nuu>"
"<tau_0 Encoding=\"DEC\">203997733934887710638541712371271015964652564562</tau_0>"
"<tau_1 Encoding=\"DEC\">306498878352083064165168696361779147057216662544</tau_1>"
"</ShuffleSecretValues>";

const char *const valid_rho_hash_values4collision =
"<ShuffleHashValues>"
"<rho_hash_value Encoding=\"DEC\">614030540099773507970899949825113536882510647294</rho_hash_value>"
"<rho_values><rho_value Encoding=\"DEC\">17</rho_value>"
"<rho_value Encoding=\"DEC\">7</rho_value>"
"<rho_value Encoding=\"DEC\">25</rho_value>"
"</rho_values>"
"</ShuffleHashValues>";

void
initialize_data ()
{
   const char data_root[] = "../../vhti/bindings/perl/examples/";

   valid_svb                    = snarf (data_root, "voter-Joe_Voter_#0/svb.xml");
   valid_svbs                   = snarf (data_root, "svbs.xml");
   valid_bb                     = snarf (data_root, "bb.xml");
   valid_rbb                    = snarf (data_root, "rbb.xml");
   valid_rbb_before             = snarf (data_root, "rbb.xml");
   valid_rbb_after              = snarf (data_root, "shuffled-rbb-#0.xml");
   valid_auth_pd                = snarf (data_root, "auth0/partial-decrypt.xml");
   valid_auth_pds               = snarf (data_root, "auth-partial-decrypts.xml");
   valid_auth_pds_4vc           = snarf (data_root, "partial-decrypts-4vc.xml");
   valid_pd_ballot_box          = snarf (data_root, "partially-decrypted-bb.xml");
   valid_sbb                    = snarf (data_root, "sbb.xml");
   valid_prvkey                 = snarf (data_root, "pollsite-private-key.xml");
   valid_pubkey                 = snarf (data_root, "pollsite-pubkey.xml");
   valid_committed_authority    = snarf (data_root, "committed-auth-0.xml");
   valid_sv_proof               = snarf (data_root, "shuffle-validity-proof-#0.xml");
   valid_pvc_boxes              = snarf (data_root, "pre-vc-boxes.xml");
   valid_vr                     = snarf (data_root, "voter-roll.xml");
   valid_authority              = snarf (data_root, "auth0.xml");
   valid_trustee_dict_comm      = snarf (data_root, "trustee-0-dict_comm.xml");
   valid_trustee_dict_secrets   = snarf (data_root, "trustee-0-revealed_dict_secrets.xml");
   valid_trustee_dict_secrets_box   = snarf (data_root, "trustee_revealed_dict_secrets_box.xml");
   valid_trustee_pubkey         = snarf (data_root, "trustee-0-pubkey.xml");
}
