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

#include <vhti/random.h>
#include <support/random_internal.h>
#include <support/support_internal.h>
#include <support/internal_error.h>
#include <misc/xml_tree.h>
#include <misc/vh_excpt.h>
#include <util/sslerror.h>
#include <string>
#include <sstream>
#include <iostream>

#include <limits.h>
#include <openssl/bn.h>

namespace VHInternal {

void
get_ij_bits(RandomIJState random_ij_state,
                        auto_BN i_index,
                        auto_BN j_index,
                        int nbits,
                        RandomIJState * return_random_ij_state,
                        RandomBits * bits)
{
   int result = 0;
   *return_random_ij_state = NULL;
   *bits = NULL;
   auto_freeing <RandomState> new_rstate = 0;
   auto_freeing <RandomBits> newbits = 0;

   VH_zero (::VHTI_validate(RANDOM_IJ_STATE, random_ij_state), BAD_RANDOM_IJ_STATE);

   get_ij_bits_internal(random_ij_state, i_index, j_index,
                        nbits, &new_rstate, &newbits);

   //Send back the same thing you got in
   *return_random_ij_state = VHTI_dup(random_ij_state);
   *bits = VHTI_dup(newbits);
}

void
get_ij_bits_internal(RandomIJState random_ij_state,
                                 auto_BN i_index,
                                 auto_BN j_index,
                                 int nbits,
                                 RandomState * return_random_state,
                                 RandomBits * bits)
{
   *return_random_state = NULL;
   *bits = NULL;
   auto_freeing <RandomState> new_rstate = 0;
   auto_freeing <RandomBits> newbits = 0;

   VH_zero (::VHTI_validate(RANDOM_IJ_STATE, random_ij_state), BAD_RANDOM_IJ_STATE);

   VHUtil::xml_tree xml_rstate(random_ij_state);

   // We're supposed to generate a true random number, but we
   // don't yet know how.
   VH_zero (xml_rstate.root ()->attribute(SOURCE_TYPE) == "TRUE", UNIMPLEMENTED);

   // Might need other tests as we add more pseudorandom number
   // generation methods.

   // Get key out of RandomState
   VHUtil::xml_node key_node = xml_rstate.root ()->e(RANDOM_SEED_KEY);
   std::string key_data = key_node->characters();
   auto_BN key_bn = BN_bin2bn((unsigned char *)key_data.c_str(),
                              key_data.size(), 0);
   VH_nonzero (key_bn, SSL_ERROR);

   // get hash of key, i, and j
   const BIGNUM * arr[] = {key_bn, i_index, j_index};
   auto_BN hashval;
   hashval = GetHashOfNBNs(arr, sizeof(arr) / sizeof(arr[0]));

   // build up new state object to pass to GetBits
   VHUtil::xml_tree xml_rstate_bar("<" RANDOM_STATE "/>");

   xml_rstate_bar.root ()->add_element(key_node->deep_copy());
   add_BN_element(xml_rstate_bar.root (), RANDOM_BLOCK, hashval, DEC);
   xml_rstate_bar.root ()->add_attribute(SOURCE_TYPE, VHInternal::SourceType);

   std::ostringstream rs_bar_stream;
   rs_bar_stream << xml_rstate_bar;

   VH_propagate (VHTI_get_bits(rs_bar_stream.str().c_str(), nbits,
                               &new_rstate, &newbits), GET_IJ_BITS);

   *return_random_state = VHTI_dup(new_rstate);
   *bits = VHTI_dup(newbits);
}

void
rand_range(auto_BN max_plus_one, 
                       VHInternal::RS &rs,
                       auto_BN & retval)
{
   int done = 0;
   int max_bits = BN_num_bits(max_plus_one);
   auto_freeing<RandomBits> newbits = 0;

   while(!done)
   {
      VH_propagate (VHTI_get_bits(rs,
                                  max_bits,
                                  rs,
                                  &newbits), RAND_RANGE_GET_BITS);

      auto_BN test_retval = xml2BN(VHUtil::xml_tree (std::string (newbits)).root());
      if (test_retval < max_plus_one)
      {
         done = 1;
         retval = test_retval;
      }
   }
}

void
rand_range2(auto_BN min,
                        auto_BN max,
                        VHInternal::RS &rs,
                        auto_BN & retval)
{
   auto_BN return_rand(NULL);

   auto_BN diff_bits;
   VH_nonzero (BN_sub(diff_bits, max, min), SSL_ERROR);

   auto_freeing<RandomState> return_random_state = 0;
   rand_range(diff_bits,
              rs,
              return_rand);

   VH_nonzero (BN_add(return_rand, return_rand, min), SSL_ERROR);
   retval = return_rand;
}

void
rand_range_ij(auto_BN max,
                          auto_BN i_index,
                          auto_BN j_index,
                          RandomIJState random_ij_state,
                          RandomState * random_state_out,
                          auto_BN & retval)
{
   * random_state_out = NULL;

   int max_bits = BN_num_bits(max);
   auto_freeing<RandomState> return_random_state = 0;
   auto_freeing<RandomBits> newbits = 0;

   get_ij_bits_internal(random_ij_state, i_index, j_index,
                        max_bits, &return_random_state, &newbits);

   auto_BN test_retval = xml2BN(VHUtil::xml_tree (std::string (newbits)).root());
   if (test_retval < max)
   {
      retval = test_retval;
   }
   else
   {
      VHInternal::RS rs (static_cast<RandomState>(return_random_state));

      rand_range(max, rs, retval);
   }

   *random_state_out = VHTI_dup(return_random_state);
}

void
rand_range_2ij(auto_BN min, auto_BN max,
                           auto_BN i_index,
                           auto_BN j_index,
                           RandomIJState random_ij_state,
                           RandomState * random_state_out,
                           auto_BN & retval)
{
   *random_state_out = NULL;
   auto_BN return_rand(NULL);

   auto_BN diff_bits;
   VH_nonzero (BN_sub(diff_bits, max, min), SSL_ERROR);

   auto_freeing<RandomState> return_random_state = 0;
   rand_range_ij(diff_bits, i_index, j_index, random_ij_state,
                 &return_random_state, return_rand);

   auto_BN new_rand;
   VH_nonzero (BN_add(new_rand, return_rand, min), SSL_ERROR);

   retval = new_rand;
   *random_state_out = VHTI_dup(return_random_state);
}

void
generate_prime(int nbits,
               auto_BN & prime,
               VHInternal::RS &rs)
{
   int done = 0;
   auto_BN final_prime;

   VH_nonzero (nbits > 2, INTERNAL_ERROR);
   
   while (!done)
   {
      auto_freeing<RandomBits> bits_xml = 0;
      VH_propagate (VHTI_get_bits(rs,
                                  nbits - 2,
                                  rs,
                                  &bits_xml),
                    GEN_PRIME_GET_BITS);

      auto_BN random_bits = xml2BN(VHUtil::xml_tree (std::string (bits_xml)).root());
      // double the random bits -- so they end in zero, and occupy
      // nbits - 1 bits.
      VH_nonzero (BN_lshift1 (random_bits, random_bits), SSL_ERROR);

      // the smallest number that has nbits ...
      VH_nonzero (BN_lshift  (final_prime, BN_value_one (), nbits - 1), SSL_ERROR);

      // now we have a number of n bits, all but the most- and
      // least-significant of which are random.
      VH_nonzero (BN_add     (final_prime, final_prime, random_bits), SSL_ERROR);

      // Might's well make it odd, since hardly any even numbers are
      // prime :)
      VH_nonzero (BN_add     (final_prime, final_prime, BN_value_one ()), SSL_ERROR);

      // now we have an odd number that is nbits.
      VH_nonzero (nbits == BN_num_bits (final_prime), INTERNAL_ERROR);
      
      // All that remains is to see if it's really prime.
      auto_BN_CTX ctx(BN_CTX_new());
      VH_nonzero (ctx, SSL_ERROR);

      switch (BN_is_prime(final_prime, 0, NULL, ctx, NULL))
      {
      case 0:
         break;
      case 1:
         done = 1;
         break;
      default:
         throw SSL_ERROR;
      }
   }

   prime = final_prime;
}

#ifndef min
#if defined (__GNUC__)
#define min(a,b) \
       ({ typeof (a) _a = (a); \
           typeof (b) _b = (b); \
         _a < _b ? _a : _b; })

#endif
#endif

// Return bits, starting with the low-order bits in the pool,
// regnenerating the pool as needed.

auto_BN
get_bits_internal (unsigned int needed_bits,
                   auto_BN _key,
                   unsigned char  fips_buffer[PRNG_STATESZ])
{
   auto_BN return_value;

   if (0 == needed_bits)
   {
      return return_value;
   }

   const unsigned int bytes_needed = needed_bits / CHAR_BIT + (needed_bits % CHAR_BIT ? 1 : 0);
   const unsigned int excess_bits = (bytes_needed * CHAR_BIT) - needed_bits;

   VHUtil::array<unsigned char> key_chars(BN_num_bytes(_key));
   BN_bn2bin(_key, key_chars);

   VHUtil::array<unsigned char> output (bytes_needed);

   const int status = FIPS186Generator (fips_buffer,
                                        key_chars,
                                        BN_num_bytes(_key),
                                        output,
                                        bytes_needed);

   VH_nonzero(ERROR_NONE == status, FIPS186Generator);
   VH_nonzero(BN_bin2bn(output, bytes_needed, return_value), BN_BIN2BN);
   VH_nonzero(BN_rshift(return_value, return_value, excess_bits), BN_RSHIFT);

   return return_value;
}

// Initialize private data members from the input string.
void
RS::_parse (const std::string &RandomState)
{
   VHUtil::safe_xml_tree rs (RandomState, RANDOM_STATE);
   VH_nonzero (VHInternal::SourceType == rs.root ()->attribute (SOURCE_TYPE),
               UNKNOWN_RANDOM_SOURCETYPE);

   m_key_string = rs.root ()->e (RANDOM_SEED_KEY)->characters ();
   VH_nonzero(BN_bin2bn ((unsigned char *) m_key_string.data (),
                         m_key_string.size (),
                         m_key_bn),
              BN_BIN2BN);

   m_current_state_xml = RandomState;

   auto_BN block(xml2BN(rs.root()->e(RANDOM_BLOCK)));
   VHUtil::array<unsigned char> block_chars(BN_num_bytes(block));

   BN_bn2bin(block, block_chars);

   memset(m_FIPS186_state, '\0', sizeof (m_FIPS186_state));


   {
      // Copy so that the last byte copied winds up at the end of
      // block_chars, even if we copy fewer bytes than sizeof
      // (m_FIPS186_state).

      int offset = sizeof (m_FIPS186_state) - BN_num_bytes(block);

      if (offset < 0)
      {
         offset = 0;
      }

      memcpy(m_FIPS186_state + offset,
             block_chars,
             min(BN_num_bytes(block),
                 sizeof (m_FIPS186_state)));
   }
}

RS::RS (const std::string & RandomState)
   : m_pending_state (0)
{
   _parse (RandomState);
}
RS::~RS ()
{
   if (m_pending_state)
   {
      VHTI_free (m_pending_state);
   }
}

RandomBits
RS::get_bits (unsigned int how_many)
{
   _maybe_consumem_pending_state ();

   RandomBits return_value = 0;

   VHUtil::xml_tree xml_rbits("<" RANDOM_BITS "/>");

   add_BN_characters (xml_rbits.root(),
                      get_bits_internal (how_many,
                                         m_key_bn,
                                         m_FIPS186_state),
                      DEC);

   return VHTI_dup(xml_rbits.str().c_str());
}

RS::operator RandomState ()
{
   _maybe_consumem_pending_state ();
         
   VHUtil::xml_tree state_tree ("<" RANDOM_STATE "/>");
   
   state_tree.root ()->add_attribute (SOURCE_TYPE, VHInternal::SourceType);
   state_tree.root ()->new_element (RANDOM_SEED_KEY)->add_characters (m_key_string);

   {
      auto_BN block;
      VH_nonzero(BN_bin2bn(m_FIPS186_state, sizeof (m_FIPS186_state), block), BN_BIN2BN);
      add_BN_element (state_tree.root (),
                      "RandomBlock",
                      block,
                      DEC);

   }
   m_current_state_xml = state_tree.str ();
   return m_current_state_xml.c_str ();
}

RS::operator RandomState *()
{
   _maybe_consumem_pending_state ();
   return &m_pending_state;
}

void
RS::_maybe_consumem_pending_state ()
{
   if (m_pending_state)
   {
      _parse (m_pending_state);
      VHTI_free (m_pending_state);
      m_pending_state = 0;
   }
}
}
