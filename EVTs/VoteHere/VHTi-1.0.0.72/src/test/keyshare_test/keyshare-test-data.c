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

#include <vhti/types.h>
#include <support_test/test-data.h>
#include <test_misc/test-misc.h>

// These are all well-formed, but invalid.
// Things used in key generation

const char *const invalid_authority = "<" BROADCAST_VALUES " />";
const char *const invalid_broadcast_values = "<" SECRET_COEFFICIENTS " />";
const char *const invalid_key_gen_parameters = "<" BROADCAST_VALUES " />";
const char *const invalid_keyshare_commitment = "<" BROADCAST_VALUES " />";
const char *const invalid_pairwise_secrets = "<" BROADCAST_VALUES " />";
const char *const invalid_random_state = "<" BROADCAST_VALUES " />";
const char *const invalid_secret_coefficients = "<" BROADCAST_VALUES " />";
const char *const invalid_seed_parameters= "<" BROADCAST_VALUES " />";

const char *valid_authority;
const char *valid_broadcast_values;
const char *valid_key_gen_parameters;
const char *valid_keyshare_commitment;
const char *valid_pairwise_secrets;
const char *valid_secret_coefficients;

const char *const valid_random_state =
"<RandomState SourceType=\"PSEUDO FROM HASH\">"
"<RandomSeedKey>"
"Some kind of random data to hash"
"</RandomSeedKey>"
"<RandomBlock Encoding=\"DEC\">"
"0"
"</RandomBlock>"
"</RandomState>";

const char *const valid_seed_parameters =
   "<SeedParameters>"
   "<NumAuth>3</NumAuth>"
   "<Threshold>2</Threshold>"
   "</SeedParameters>";

void
initialize_data ()
{
   const char data_root[] = "../../vhti/bindings/perl/examples/";

   valid_authority              = snarf (data_root, "auth0.xml");
   valid_broadcast_values       = snarf (data_root, "broadcast-values.xml");
   valid_key_gen_parameters     = snarf (data_root, "kgp.xml");
   valid_keyshare_commitment    = snarf (data_root, "auth0-ksc.xml");
   valid_pairwise_secrets       = snarf (data_root, "auth0/pws.xml");
   valid_secret_coefficients    = snarf (data_root, "auth0/secret-coefficients.xml");
}
