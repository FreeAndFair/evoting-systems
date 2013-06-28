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

#ifndef RANDOM_INTERNAL_H
#define RANDOM_INTERNAL_H

#include "vhti/support.h"
#include "misc/safe_xml_tree.h"
#include "support/bignum.h"
extern "C" {
#include "fipsprng.h"
}
#include <cassert>
#include <sstream>

#ifdef __cplusplus

namespace VHInternal{
const std::string SourceType = "PSEUDO FROM HASH";
class RS;

enum LOCK {
   Q_VAL,
      R1_VAL,
      R2_VAL,
      R3_VAL,
      R4_VAL,
      R5_VAL
};

void
get_ij_bits(RandomIJState random_ij_state,
            auto_BN i_index,
            auto_BN j_index,
            int nbits,
            RandomIJState * return_random_ij_state,
            RandomBits * bits);

void
get_ij_bits_internal(RandomIJState random_ij_state,
                     auto_BN i_index,
                     auto_BN j_index,
                     int nbits,
                     RandomState * return_random_state,
                     RandomBits * bits);

void
rand_range(auto_BN max,
           VHInternal::RS &,
           auto_BN & retval);

void
rand_range2(auto_BN min,
            auto_BN max,
            VHInternal::RS &rs,
            auto_BN & retval);

void
rand_range_ij(auto_BN max,
              auto_BN i_index,
              auto_BN j_index,
              RandomIJState random_state,
              RandomState * random_state_out,
              auto_BN & retval);
void
rand_range_2ij(auto_BN min, auto_BN max,
               auto_BN i_index,
               auto_BN j_index,
               RandomIJState random_state,
               RandomState * random_state_out,
               auto_BN & retval);

void
generate_prime(int nbits,
               auto_BN & prime,
               VHInternal::RS &rs);

// This isn't a member of class RS because it's easier to test this
// way.
auto_BN get_bits_internal (unsigned int needed_bits,
                           auto_BN key,
                           unsigned char fips_buffer[PRNG_STATESZ]);

class RS {

   void _parse (const std::string &RandomState);
      
public:
   RS (const std::string & RandomState);

   ~RS ();

   RandomBits get_bits (unsigned int how_many);

   operator RandomState ();
   operator RandomState *();

private:
   unsigned char    m_FIPS186_state[PRNG_STATESZ];

   // This is the same information as m_FIPS186_state, but expressed
   // as XML.
   std::string m_current_state_xml;
   
   // The secret key which makes the pseudo-random numbers impossible
   // to guess
   std::string m_key_string;
   
   // Same information as m_key_string, but expressed as a BIGNUM
   auto_BN m_key_bn;

   // We want to allow this class to be treated as a char *, so that
   // we can pass it to C functions that expect a RandomState *, so
   // that those functions can write XML onto the pointer.  When those
   // functions do so, they will be modifying m_pending_state, and we
   // will make sure that, if m_pending_state is not 0, we use it
   // instead of m_current_state_xml or m_FIPS186_state.
   RandomState m_pending_state;
   void _maybe_consumem_pending_state ();
};
}

#endif  /* __cplusplus */

#endif  /* __RANDOM_INTERNAL_H */
