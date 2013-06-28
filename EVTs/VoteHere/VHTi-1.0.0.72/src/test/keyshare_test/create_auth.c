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
#include <stdio.h>
#include "keyshare_test.h"
#include <vhti/keyshare_util.h>
#include <support_test/test-data.h>

const char *valid_pubkey = "<GeneralPurposePublicKey><IdentInfo>Noone in particular</IdentInfo>"
"<SigningPublicKey>-----BEGIN PUBLIC KEY-----\n"
"MIIBtjCCASsGByqGSM44BAEwggEeAoGBAMelsCWNBY4uZsArVsvy4PBZKJJ9NjKf\n"
"NGzXfHekzbSAOIuMfsYnfpGoRj7CrXieZbM8FGIFf96pbL+bwGzoiaasBpN5eDul\n"
"ajrzeevxSDiRBjE+JMDhAdWT+ykxeltQwEDvSfg47b7d9sHn35fdFk5ODDaXEVo1\n"
"GLIcmNBnBlUbAhUAsb92U4ajPkTVPS4pdHYNVFyeI9cCgYANaxDN6TeSajIEvyVr\n"
"iF9jMrtgCGHpwzvnEyV4N9RtbsFKdiL6bEd8Hoa+xTl57ohKO15lndZA+LiSBRSc\n"
"W217EpuQ70fqqrWefCsCJEL/zcKJCYPBnTHzlmvopfTtGLAXYjA6OhYG3C/lVrr4\n"
"aZhiA2+Lmnia7RalG7M/33D8dAOBhAACgYAqE34OYH6RrmkW4AoIUgW4dytuFxYo\n"
"AkI7ola07vYAOQsoxtFV2gO4m9/TraVyCz/xPWHz2zFGs2wLIvJ9yvJXW68TPjMN\n"
"TCXJ3IB2ZY4bG7s7zOxzhxqqQZhvPcU8VdGlj6C+R+IBGzEJucE7XyrNdMiOFIM5\n"
"su4+n9leH3f6lg==\n"
"-----END PUBLIC KEY-----\n"
"</SigningPublicKey><EncryptionPublicKey>-----BEGIN PUBLIC KEY-----\n"
"MIGdMA0GCSqGSIb3DQEBAQUAA4GLADCBhwKBgQDAKXdA92W/H2r21ce/2ZfIObhu\n"
"GyTK/4m5vkGdbJcmuiXiIH7RVaNsmaQoLd7KKYoitIy1YPyznhCVrUtAYVqns1+d\n"
"l5NvBUTg+VzRF81h1z/L+zK+6csDg9N0eN8cxJExQOL4XiOayKAY7+L+NtN2ks68\n"
"Tll3Kd/PqY/COFrNBwIBAw==\n"
"-----END PUBLIC KEY-----\n"
"</EncryptionPublicKey></GeneralPurposePublicKey>";

void
create_authority_validation (CuTest *tc)
{
   char * a;
   char * rs;
   char * pr;
   int result = VHTI_create_authority ("Mr. Moto",
                                       valid_key_gen_parameters,
                                       valid_random_state,
                                       valid_pubkey,
                                       &pr,
                                       &a,
                                       &rs);
   CuAssert (tc,
             "VHTI_create_authority should have succeeded",
             0 == result);

   CuAssert (tc,
             "VHTI_create_authority should not have returned a GeneralPurposePrivateKey, since we passed in our own GeneralPurposePublicKey",
             (NULL == pr));

   VHTI_free (a);
   VHTI_free (rs);

   {
      result = VHTI_create_authority ("Sam Spade",
                                      valid_key_gen_parameters,
                                      valid_random_state,
                                      NULL,
                                      &pr,
                                      &a,
                                      &rs);
      CuAssert (tc,
                "VHTI_create_authority should have succeeded",
                0 == result);

      CuAssertPtrNotNull (tc, pr);

      CuAssert (tc,
                "VHTI_create_authority should have returned a GeneralPurposePrivateKey, since we did not pass in our own GeneralPurposePublicKey",
                0 == (VHTI_validate (GENERAL_PURPOSE_PRIVATE_KEY,
                                     pr)));

      VHTI_free (pr);
      VHTI_free (a);
      VHTI_free (rs);
   }

   /* just like the above, except using an empty string instead of NULL. */
   {
      result = VHTI_create_authority ("Sam Spade",
                                      valid_key_gen_parameters,
                                      valid_random_state,
                                      "",
                                      &pr,
                                      &a,
                                      &rs);
      CuAssert (tc,
                "VHTI_create_authority should have succeeded",
                0 == result);

      CuAssertPtrNotNull (tc, pr);

      CuAssert (tc,
                "VHTI_create_authority should have returned a GeneralPurposePrivateKey, since we did not pass in our own GeneralPurposePublicKey",
                0 == (VHTI_validate (GENERAL_PURPOSE_PRIVATE_KEY,
                                     pr)));

      VHTI_free (pr);
      VHTI_free (a);
      VHTI_free (rs);
   }
}
