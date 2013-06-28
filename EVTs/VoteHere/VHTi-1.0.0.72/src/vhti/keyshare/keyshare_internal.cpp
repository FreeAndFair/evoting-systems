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

#pragma warning(disable: 4786)
#include "keyshare/keyshare_internal.h"
#include <misc/xml_tree.h>
#include <support/support_internal.h>

#include <string>
#include <sstream>
#include <set>

namespace {

void
collect_prints (VHUtil::xml_node node,
                std::set<std::string> &prints_seen)
{
   if (node->has_attribute (AUTH_FINGERPRINT))
   {
      const std::string &the_print = node->attribute (AUTH_FINGERPRINT);
      VH_nonzero (prints_seen.find (the_print) == prints_seen.end (), DUPLICATE_AUTH_FINGERPRINT);

      prints_seen.insert (the_print);
   }

   for (int i=0; i < node->element_count(); i++)
      collect_prints (node->element (i), prints_seen);
}

void
collect_orders (VHUtil::xml_node node,
                std::set<unsigned int> &orders_seen,
                const unsigned int threshold)
{
   if (node->has_attribute (ORDER))
   {
      const unsigned int the_order = VHInternal::int_from_attribute (node, ORDER);
      VH_zero (the_order < 0, NEGATIVE_ORDER);
      VH_nonzero (the_order < threshold, ORDER_NOT_LESS_THAN_THRESHOLD);
      VH_nonzero (orders_seen.find (the_order) == orders_seen.end (), DUPLICATE_ORDER);

      orders_seen.insert (the_order);
   }

   for (int i=0; i < node->element_count (); i++)
      collect_orders (node->element (i), orders_seen, threshold);
}
}

namespace VHInternal {

void
get_keygen_parameters (KeyGenParameters key_gen_parameters,
                       auto_BN & pm, auto_BN & qm,
                       auto_BN & gen, int & na, int & th)
                                   
{
   // An xml tree from the key_gen_parameters input
   VHUtil::xml_tree xml_kgp(key_gen_parameters);
   // The root node of xml_kgp
   VHUtil::xml_node root_kgp(xml_kgp.root());
   // The node containing the CryptoGroupParameters
   VHUtil::xml_node node_cgp = root_kgp->e(CRYPTO_GROUP_PARAMETERS);

   // Find ElectionModulus value
   pm = xml2BN(node_cgp->e(ELECTION_MODULUS));
   // Find ElectionSubgroupModulus value
   qm = xml2BN(node_cgp->e(ELECTION_SUBGROUP_MODULUS));
   // Find ElectionSubgroupGenerator value
   gen = xml2BN(node_cgp->e(ELECTION_SUBGROUP_MEMBER));
   // Find number of authorities
   na = VHInternal::int_from_characters (root_kgp->e(NUM_AUTH));

   // Find Threshold value
   th = VHInternal::int_from_characters (root_kgp->e(THRESHOLD));
}

void
sanity_check_auth_fingerprints (unsigned int num_auth,
                                VHUtil::xml_tree &arbitrary_xml)
{
   std::set<std::string> fingerprints_seen;
   collect_prints (arbitrary_xml.root (), fingerprints_seen);

   if (fingerprints_seen.size () != num_auth)
      VHUtil::cout () << arbitrary_xml;

   VH_nonzero (fingerprints_seen.size () == num_auth, WRONG_NUMBER_OF_AUTHORITIES);
}

void
sanity_check_orders (unsigned int threshold,
                     VHUtil::xml_tree &arbitrary_xml)
{
   std::set<unsigned int> orders_seen;
   collect_orders (arbitrary_xml.root (), orders_seen, threshold);

   if (orders_seen.size () != threshold)
      VHUtil::cout () << arbitrary_xml;

   VH_nonzero (orders_seen.size () == threshold, NUMBER_OF_ORDERS_NOT_EQUAL_TO_TAB_THRESHOLD);
}
}
