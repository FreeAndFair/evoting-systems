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
#include <support/random_internal.h>
#include "vhti/random.h"
#include "vhti/permutation.h"
#include <support/bignum.h>
#include "misc/xml_tree.h"
#include "misc/vh_cout.h"
#include <support/support_internal.h>
#include <support/internal_error.h>
#include <misc/vh_excpt.h>

#include <string>
#include <sstream>

int
main()
{
   int result = 0;
   try
   {
      // Demonstrate random number functions

      // First build up a RandomIJState object
      VHUtil::xml_tree xml_rij_state("<RandomIJState/>");
      VHUtil::xml_node root_rij_state = xml_rij_state.root();
      root_rij_state->add_attribute(SOURCE_TYPE, VHInternal::SourceType);

      VHUtil::xml_tree xml_key("<RandomSeedKey/>");
      VHUtil::xml_node root_key = xml_key.root();
      // You need a key
      std::string key_data("Andrew says: Some kind of random data to hash");
      root_key->add_characters(key_data);
      root_rij_state->add_element(root_key->deep_copy());

      std::ostringstream stream_rij_state;
      stream_rij_state << xml_rij_state;

      auto_freeing<RandomIJState> return_random_ij_state = 0;
      auto_freeing<RandomBits> ij_bits = 0;
      auto_BN i_index;
      auto_BN j_index;
      BN_set_word(i_index, 3);
      BN_set_word(j_index, 5);
      VHInternal::get_ij_bits(stream_rij_state.str().c_str(), i_index, j_index,
                              55, &return_random_ij_state, &ij_bits);

      std::string rrs(return_random_ij_state);
      std::string bs(ij_bits);

      printf("\n\nRETURN_RANDOM_IJ_STATE is %s", static_cast<const char *>(return_random_ij_state));
      printf("\n\nIJBITS is %s", static_cast<const char *>(ij_bits));
      VHUtil::cout() << "RETURN_RANDOM_IJ_STATE is " << rrs << std::endl;
      VHUtil::cout() << "IJBITS is " << bs << std::endl;

      // You can do this test even if the above one failed.
      // Test VHTI_get_bits
      std::ostringstream key_stream;
      key_stream << xml_key;
   
      auto_freeing <RandomState> init_random_state = 0;
      result = VHTI_generate_random_state(key_stream.str().c_str(), &init_random_state);
   
      auto_freeing<RandomIJState> return_random_state = 0;
      auto_freeing<RandomBits> bits = 0;
   
      result = VHTI_get_bits(init_random_state,
                             VHInternal::digest_bits,
                             &return_random_state,
                             &bits);
   
      printf("\n\nRETURN_RANDOM_STATE is %s", static_cast<const char *>(return_random_state));
      printf("\n\nBITS is %s", static_cast<const char *>(bits));

      if (result)
      {
         printf("\nUh oh.  VHTI_GetBits failed.");
         exit(1);
      }

      // You can do this test even if the above one failed
      // Test permutations

      auto_freeing<Permutation> permutation = 0;
      {
         const std::string rs_tmp(return_random_state);
         result = VHTI_get_permutation(rs_tmp.c_str(), 12, &permutation, &return_random_state);
      }
      printf("\n\nPERMUTATION is %s", static_cast<const char *>(permutation));

      if (result)
      {
         printf("\nUh oh.  VHTI_GetPermutation failed.");
         exit(1);
      }

      // You can do this test even if the above one failed.
      // Test VHTI_rand_range
      printf("\n\nTesting rand_range");

      auto_BN return_rand(NULL);
      BIGNUM * max = BN_new();
      BN_dec2bn(&max, "45");
      VHInternal::RS rs (static_cast<const char *>(return_random_state));
      VHInternal::rand_range(max, rs, return_rand);

      std::string rr1_str = BN_bn2dec(return_rand);
      printf("\n\nRANDOM NUMBER is %s", rr1_str.c_str());

      // You can do this test even if the above one failed.
      // Test VHTI_rand_range2
      printf("\n\nTesting rand_range2");
      BIGNUM * newmax = BN_new();
      BN_dec2bn(&newmax, "125");
      BIGNUM * min = BN_new();
      BN_dec2bn(&min, "75");
      VHInternal::rand_range2(min, newmax, rs, return_rand);

      std::string rr2_str = BN_bn2dec(return_rand);
      printf("\n\nRANDOM NUMBER is %s", rr2_str.c_str());

      printf("\n\nTesting fixed_mod_exp\n\n");
      auto_BN nuu; // nuu is zero
      auto_BN gen;
      BN_set_word(gen, 17);
      auto_BN pm;
      BN_set_word(pm, 47);
      auto_BN_CTX ctx(BN_CTX_new());
      std::string gen_str = BN_bn2dec(gen);
      std::string pm_str = BN_bn2dec(pm);
      printf("The base gen is %s\n\n", gen_str.c_str());
      printf("The modulus pm is %s\n\n", pm_str.c_str());
      auto_BN GValue; // Generate G_value from nu
      VHInternal::fixed_mod_exp(GValue, gen, nuu, pm, ctx);
      
      printf("Expect GValue to be 1 because the exponent is 0.\n");
      std::string G_str = BN_bn2dec(GValue);
      printf("GValue is %s\n\n", G_str.c_str());
      if ( !(BN_is_one(GValue)) )
      {
         printf("Uh oh, raising to an exponent of zero had problems\n");
      }
      
      printf("Make exponent another number but keep base the same.\n\n");
      BN_set_word(nuu, 6);
      std::string nuu_str = BN_bn2dec(nuu);
      VHInternal::fixed_mod_exp(GValue, gen, nuu, pm, ctx);
      printf("Expect GValue to be 14 because the exponent is 6.\n");
      G_str = BN_bn2dec(GValue);
      printf("GValue is %s\n\n", G_str.c_str());
      if (G_str != "14")
      {
         printf("Uh oh, raising to an exponent had problems\n");
      }
      
      printf("Now use bignums.\n\n");
      // Generate p, q, and g from scratch
      // Generate primes p, q, and r, where q and r are relatively prime,
      // and p = qr + 1.
      auto_BN qm;
      VH_nonzero (BN_generate_prime(qm,
                                    VHInternal::digest_bits,
                                    0,
                                    NULL,
                                    NULL,
                                    NULL,
                                    NULL),
                  BN_GENERATE_PRIME);
      // r = (p-1 / q),  make sure  r / q has a remainder
      auto_BN r_val;
      
      // The remainder
      auto_BN rem;
      auto_BN one_bn; // An auto_BN with the value of 1
      BN_one(one_bn);
      while (BN_is_zero(rem))
      {
         VH_nonzero (BN_generate_prime(pm, 1024, 0, qm, NULL, NULL, NULL),
                     BN_GENERATE_PRIME);
         auto_BN tmp_sub; // p - 1
         VH_nonzero (BN_sub(tmp_sub, pm, one_bn), BN_SUB);
         VH_nonzero (BN_div(r_val, NULL, tmp_sub, qm, ctx), BN_DIV);
         VH_nonzero (BN_div(NULL, rem, r_val, qm, ctx), BN_DIV);
      }
      // A value in Zp*
      auto_BN tmp_gen(NULL);
      VHInternal::rand_range2 (one_bn, pm, rs, tmp_gen);
      
      // Our generator is this temporary number raised to (p-1)/q = r
      // Compute exponent
      VH_nonzero (BN_mod_exp(gen, tmp_gen, r_val, pm, ctx), BN_MOD_EXP);
      
      // Generate random nu in Zq*
      VHInternal::rand_range2(one_bn, qm, rs, nuu);
      VHInternal::fixed_mod_exp(GValue, gen, nuu, pm, ctx);
      gen_str = BN_bn2dec(gen);
      pm_str = BN_bn2dec(pm);
      nuu_str = BN_bn2dec(nuu);
      G_str = BN_bn2dec(GValue);
      printf("The base gen is %s\n\n", gen_str.c_str());
      printf("The modulus pm is %s\n\n", pm_str.c_str());
      printf("The exponent nuu is %s\n\n", nuu_str.c_str());
      printf("GValue is %s\n\n", G_str.c_str());
      
      printf("Make exponent another number but keep base the same.\n\n");
      VHInternal::rand_range2(one_bn, qm, rs, nuu);
      VHInternal::fixed_mod_exp(GValue, gen, nuu, pm, ctx);
      nuu_str = BN_bn2dec(nuu);
      printf("The exponent nuu is %s\n\n", nuu_str.c_str());
      G_str = BN_bn2dec(GValue);
      printf("GValue is %s\n\n", G_str.c_str());
   }
   catch (const VHUtil::Exception & e)
   {
      VHTI_set_last_error(e);
      result = e.getResultNo();
   }

   printf("\n\nSupport sample FINISHED EXECUTING.\n");
   return result;
}
