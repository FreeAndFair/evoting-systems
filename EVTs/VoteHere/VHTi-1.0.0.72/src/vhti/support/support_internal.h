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

#ifndef SUPPORT_INTERNAL_H
#define SUPPORT_INTERNAL_H

#include "vhti/support.h"
#include "support/bignum.h"
#include "support/mutex.h"
#include <map>
#include <vector>
#include <string>
#include <istream>

#ifdef __cplusplus

/* define this to print simple timings of fixed_mod_exp versus BN_mod_exp */
#define MOD_EXP_STATS

#if defined (MOD_EXP_STATS)
extern "C" { void dump_stats (); }
#endif

namespace VHInternal{ 

/* This one mutex controls access to all the library's global
 * variables. */
extern VHUtil::Mutex g_mutex;

void
check_group_membership (auto_BN & value,
                        auto_BN & pm,
                        auto_BN & qm);

void
fixed_mod_exp (auto_BN & retval,
               const auto_BN & base,
               const auto_BN & exp,
               const auto_BN & modulus,
               auto_BN_CTX & ctx);

void
get_election_parameters(const std::string &input,
                        auto_BN & pm,
                        auto_BN & qm,
                        auto_BN & gen,
                        auto_BN & ePublicKey);
void
get_election_parameters2(VHUtil::xml_node &input,
                         auto_BN & pm,
                         auto_BN & qm,
                         auto_BN & gen,
                         auto_BN & ePublicKey);

/* parse integers from XML, and provide decent error messages on failure. */
long int
   int_from_characters (VHUtil::xml_node n);

long int
   int_from_attribute (VHUtil::xml_node n,
                       const std::string &attribute_name);

/* these are called by the above. */
long int
   str2num (const std::string &s,
            const std::string &error_message = "");

long int
   read_int (std::istream &s,
             const std::string &error_message = "");
}

#endif  /* __cplusplus */

#endif  /* __SUPPORT_INTERNAL_H */
