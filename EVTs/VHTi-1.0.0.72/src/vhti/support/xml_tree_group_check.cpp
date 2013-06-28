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

#include "xml_tree_group_check.h"
#include <misc/safe_xml_tree.h>
#include "support_internal.h"
#include <set>

namespace VHUtil {

std::set< std::string > xml_tree_group_check::g_group_elements;

void
xml_tree_group_check::init (auto_BN & pm,
                            auto_BN & qm,
                            auto_BN & gen,
                            auto_BN & ePublicKey)
{
   if ( pm == NULL || qm == NULL || gen == NULL )
   {
      // Get parameters
      VHInternal::get_election_parameters(*this, pm, qm, gen, ePublicKey);
   }

   // Traverse and check for group membership
   VHUtil::xml_node root_node = this->root();
   check_tree4gm(root_node, pm, qm);
}

xml_tree_group_check::xml_tree_group_check (const std::string & signed_input,
                                            const std::string & expected_root_element_name,
                                            const std::string & pub_key,
                                            auto_BN & pm, auto_BN & qm,
                                            auto_BN & gen, auto_BN & ePublicKey)
   :                            // we have to initialize our xml_tree
                                // with something -- even though we
                                // expect to replace it later
     xml_tree("<Bogosity/>")
{
   VHUtil::safe_xml_tree checked (signed_input, expected_root_element_name, pub_key);

   this->root ()-> erase ();
   this->m_root = checked.root ()->deep_copy ();

   init (pm, qm, gen, ePublicKey);
}

xml_tree_group_check::xml_tree_group_check (const std::string &unsigned_input,
                                            auto_BN & pm,
                                            auto_BN & qm,
                                            auto_BN & gen,
                                            auto_BN & ePublicKey )
   : xml_tree (unsigned_input)
{
   init (pm, qm, gen, ePublicKey);
}


void
xml_tree_group_check::check_tree4gm( xml_node nn, auto_BN pm, auto_BN qm)
{
   if (g_group_elements.size() == 0)
   {
      populate_set();
   }

   if ( g_group_elements.find(nn->name()) != g_group_elements.end() )
   {
      auto_BN in_bn = xml2BN(nn);
      VHInternal::check_group_membership(in_bn, pm, qm);
   }

   for (int i=0; i<nn->element_count(); i++)
   {
      check_tree4gm( nn->element(i), pm, qm);
   }
}

// Always use macros here instead of string constants, when possible,
// to reduce the risk of typos.
void 
xml_tree_group_check::populate_set()
{
   g_group_elements.insert (A_VALUE);
   g_group_elements.insert (ANSWER_MARK);
   g_group_elements.insert (BIG_GAMMA);
   g_group_elements.insert (BIG_THETA);
   g_group_elements.insert (C_VALUE);
   g_group_elements.insert (G_VALUE);
   g_group_elements.insert (KEY_SHARE_COMMITMENT);
   g_group_elements.insert (LAMBDA_1);
   g_group_elements.insert (LAMBDA_2);
   g_group_elements.insert (OMEGA);
   g_group_elements.insert (THETA_VALUE);
   g_group_elements.insert (U_VALUE);
   g_group_elements.insert (W_VALUE);
   g_group_elements.insert (X_VALUE);
   g_group_elements.insert (Y_VALUE);
}

}
