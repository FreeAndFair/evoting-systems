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

#include "vhti/gen_bsns.h"
#include "vhti/random.h"
#include <support/internal_error.h>
#include <support/random_internal.h>
#include <support/support_internal.h>
#include <support/bignum.h>
#include <misc/xml_tree.h>
#include <string>
#include <sstream>
#include <set>

namespace {
   // How many RandomBits we want
   const int num_bits = 32;

   // Think up a bunch of *distinct* random numbers, add the magic
   // offset to them, then stick them into a new
   // BALLOT_SEQUENCE_NUMBER element in the XML tree.
   void
   add_unique_bsns (VHInternal::RS &rs,
                    const auto_BN &offset,
                    int how_many,
                    std::set<auto_BN> &used_bsns,
                    VHUtil::xml_node destination)
   {
      for (;
           how_many;
           how_many--)
      {
         auto_BN bsn; // The value of the BallotSequenceNumber
         do {
            // The RandomBits we will generate
            auto_freeing <RandomBits> random_bits = rs.get_bits (num_bits);
            VH_nonzero (BN_add (bsn,
                                offset,
                                xml2BN(VHUtil::xml_tree ((const char *) random_bits).root())), BN_ADD);
         } while (used_bsns.end()
                  !=
                  used_bsns.find(bsn));

         add_BN_element (destination, BALLOT_SEQUENCE_NUMBER, bsn, DEC);
         used_bsns.insert (bsn);
      }
   }
}

int
VHTI_generate_bsns (ElectionID eid,
                    PrecinctID pid,
                    int numAuthorized,
                    int numProvisional,
                    RandomState random_state,
                    BallotSequenceNumbers * authorized_bsns,
                    BallotSequenceNumbers * provisional_bsns,
                    RandomState *random_state_out)
{
   int result = 0; // Assume success until told otherwise

   *authorized_bsns = NULL;
   *provisional_bsns = NULL;
   *random_state_out = NULL;
   
   try
   {
      VH_zero (::VHTI_validate(ELECTION_ID, eid)          , VALIDATION_FAILURE);
      VH_zero (::VHTI_validate(PRECINCT_ID, pid)          , VALIDATION_FAILURE);         
      VH_zero (::VHTI_validate(RANDOM_STATE, random_state), VALIDATION_FAILURE);

      // A RandomState object
      VHInternal::RS rs (random_state);

      auto_BN bn_eid; // A BIGNUM eid
      auto_BN bn_pid; // A BIGNUM pid
      VH_nonzero (BN_set_word(bn_eid, VHInternal::int_from_characters (VHUtil::xml_tree (eid).root ())), BN_SET_WORD);
      VH_nonzero (BN_set_word(bn_pid, VHInternal::int_from_characters (VHUtil::xml_tree (pid).root ())), BN_SET_WORD);
      
      // We are allowing 32 bits for the eid, 32 bits for the pid, and
      // 32 bits for a random number tacked onto the end.  Since eids
      // are probably only a few bits long, our result will probably
      // be only a few bits more than 64 bits long.  Ultimately our
      // BSN will look like this:

      // 00000000eid00000000pidrandomrandom
      // |<---32--->|<---32--->|<---32--->|

      // Here we generate the upper, non-random, 64 bits.
      auto_BN eid_pid_shifted (bn_eid);
      VH_nonzero (BN_lshift (eid_pid_shifted, eid_pid_shifted, num_bits), BN_LSHIFT);
      VH_nonzero (BN_add    (eid_pid_shifted, eid_pid_shifted, bn_pid  ), BN_ADD);
      VH_nonzero (BN_lshift (eid_pid_shifted, eid_pid_shifted, num_bits), BN_LSHIFT);
      
      // A set to keep track of bsns we have already used
      std::set<auto_BN> used_bsns;

      // An xml tree to hold the authorized BallotSequenceNumbers
      VHUtil::xml_tree xml_auth_bsns("<" BALLOT_SEQUENCE_NUMBERS "/>");
      add_unique_bsns (rs, eid_pid_shifted, numAuthorized, used_bsns, xml_auth_bsns.root ());
      VH_assert (numAuthorized == used_bsns.size ());

      *authorized_bsns = VHTI_dup(xml_auth_bsns.str().c_str());
      
      // An xml tree to hold the provisional BallotSequenceNumbers
      VHUtil::xml_tree xml_prov_bsns("<" BALLOT_SEQUENCE_NUMBERS "/>");
      add_unique_bsns (rs, eid_pid_shifted, numProvisional, used_bsns, xml_prov_bsns.root());
      VH_assert (numAuthorized + numProvisional == used_bsns.size ());

      *provisional_bsns = VHTI_dup(xml_prov_bsns.str().c_str());

      *random_state_out = VHTI_dup(rs);
   }
   catch (const VHUtil::Exception & e)
   {
      VHTI_set_last_error(e);
      result = e.getResultNo();
   }
   return result;
}
