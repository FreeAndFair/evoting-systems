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

#ifndef TEST_DATA_H
#define TEST_DATA_H

#ifdef __cplusplus
extern "C"
{
#endif

extern const char *const   valid_XML_plaintext;          
extern const char *const   valid_answer_ref;
extern const char *        valid_auth_pd;
extern const char *        valid_auth_pds;
extern const char *        valid_auth_pds_4vc;
extern const char *        valid_authority;
extern const char *const   valid_ballot_secrets;
extern const char *        valid_ballot_skeleton;
extern const char *        valid_bb;
extern const char *        valid_broadcast_values;
extern const char *const   valid_bsn;
extern const char *const   valid_bsns;
extern const char *        valid_ce_parameters;
extern const char *const   valid_cert;
extern const char *        valid_cg_parameters;
extern const char *        valid_clear_text_ballot;
extern const char *        valid_committed_authority;
extern const char *const   valid_display_info;
extern const char *const   valid_election_id;
extern const char *const   valid_election_node;
extern const char *const   valid_encoding;
extern const char *const   valid_ident_info;
extern const char *        valid_key_gen_parameters;
extern const char *        valid_keyshare_commitment;
extern const char *const   valid_keytype;
extern const char *const   valid_modular_int;
extern const char *const   valid_non_XML_plaintext;
extern const char *        valid_pairwise_secrets;
extern const char *const   valid_password;
extern const char *        valid_pd_ballot_box;
extern const char *const   valid_permutation;
extern const char *const   valid_precinct_id;
extern const char *const   valid_prng;
extern const char *        valid_prvkey;
extern const char *        valid_pubkey;
extern const char *        valid_pvc_boxes;
extern const char *const   valid_pw_encrypted_data;
extern const char *const   valid_random_ij_state;
extern const char *const   valid_random_seed_key;
extern const char *const   valid_random_state;
extern const char *        valid_rbb;
extern const char *        valid_rbb_after;
extern const char *        valid_rbb_before;
extern const char *const   valid_rho_hash_values4collision;
extern const char *        valid_sbb;
extern const char *        valid_secret_coefficients;
extern const char *const   valid_secret_key;
extern const char *const   valid_secret_share;
extern const char *const   valid_secret_shuffle_values_4b1_collsion;
extern const char *const   valid_secret_shuffle_values_4b2_collsion;
extern const char *const   valid_secret_shuffle_values_4r_collsion;
extern const char *const   valid_seed_parameters;
extern const char *const   valid_signature;
extern const char *const   valid_signature;
extern const char *const   valid_signed_status_query_struct;
extern const char *        valid_sigpub;
extern const char *        valid_sv_proof;
extern const char *        valid_svb;
extern const char *        valid_svbs;
extern const char *        valid_trustee_dict_comm;
extern const char *        valid_trustee_dict_secrets;
extern const char *        valid_trustee_dict_secrets_box;
extern const char *        valid_trustee_pubkey;
extern const char *const   valid_vkey;
extern const char *const   valid_vkeys;
extern const char *        valid_vote_receipt;
extern const char *        valid_vote_receipt_data;
extern const char *const   valid_voted_answer;
extern const char *        valid_vr;
extern const char *const   valid_vv_ballot;
extern const char *const invalid_answer_ref;
extern const char *const invalid_auth_pd;
extern const char *const invalid_auth_pds;
extern const char *const invalid_auth_pds_4vc;
extern const char *const invalid_authority;
extern const char *const invalid_ballot_secrets;
extern const char *const invalid_ballot_skeleton;
extern const char *const invalid_bb ;
extern const char *const invalid_broadcast_values;
extern const char *const invalid_bsn;
extern const char *const invalid_bsns;
extern const char *const invalid_ce_parameters;
extern const char *const invalid_cert;
extern const char *const invalid_cg_parameters;
extern const char *const invalid_clear_text_ballot;
extern const char *const invalid_committed_authority;
extern const char *const invalid_display_info;
extern const char *const invalid_election_id;
extern const char *const invalid_election_node;
extern const char *const invalid_encoding;
extern const char *const invalid_encrypted_data;
extern const char *const invalid_ident_info;
extern const char *const invalid_key_gen_parameters;
extern const char *const invalid_keyshare_commitment;
extern const char *const invalid_keytype;
extern const char *const invalid_modular_int;
extern const char *const invalid_pairwise_secrets;
extern const char *const invalid_password;
extern const char *const invalid_pd_ballot_box;
extern const char *const invalid_permutation;
extern const char *const invalid_precinct_id;
extern const char *const invalid_prng;
extern const char *const invalid_prvkey;
extern const char *const invalid_pubkey;
extern const char *const invalid_pvc_boxes;
extern const char *const invalid_pw_encrypted_data;
extern const char *const invalid_random_ij_state;
extern const char *const invalid_random_seed_key;
extern const char *const invalid_random_state;
extern const char *const invalid_rbb;
extern const char *const invalid_rbb_after;
extern const char *const invalid_rbb_before;
extern const char *const invalid_sbb;
extern const char *const invalid_secret_coefficients;
extern const char *const invalid_secret_key;
extern const char *const invalid_secret_share;
extern const char *const invalid_seed_parameters;
extern const char *const invalid_signature;
extern const char *const invalid_signed_document;
extern const char *const invalid_signed_status_query_struct;
extern const char *const invalid_sigpub;
extern const char *const invalid_sv_proof;
extern const char *const invalid_svb;
extern const char *const invalid_svbs;
extern const char *const invalid_trustee_dict_comm;
extern const char *const invalid_trustee_dict_secrets;
extern const char *const invalid_trustee_dict_secrets_box;
extern const char *const invalid_trustee_pubkey;
extern const char *const invalid_vkey;
extern const char *const invalid_vkeys;
extern const char *const invalid_vote_receipt;
extern const char *const invalid_vote_receipt_data;
extern const char *const invalid_voted_answer;
extern const char *const invalid_vr ;
extern const char *const invalid_vv_ballot;


// This isn't even well-formed.
extern const char *const not_xml;

#ifdef __cplusplus
}
#endif

#endif
