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
#include <misc/xml_tree.h>
#include <misc/vh_excpt.h>
#include <misc/safe_xml_tree.h>
#include <support/internal_error.h>
#include <vhti/support.h>
#include <vhti/sign.h>
#include <pki/pki_internal.h>
#include <string>

namespace VHUtil {
safe_xml_tree::safe_xml_tree (const std::string &possibly_signed_xml,
                              const std::string &expected_root_element_name,
                              const std::string &pub_key)
   : xml_tree (possibly_signed_xml, xml_tree::THROW)
{
   const std::string &actual_root_name = this->root ()->name ();
   const xml_tree::node *sig_node = this->root ()->element (SIGNATURE);

   if (sig_node
       &&
       actual_root_name.size () > VHInternal::signed_xml_root_element_prefix.size ()
       &&
       VHInternal::signed_xml_root_element_prefix == actual_root_name.substr (0, VHInternal::signed_xml_root_element_prefix.size ()))
   {
      const std::string signed_data (this->root ()->e (SIGNED_DATA)->characters ());
      auto_freeing<CheckResults> c_result = 0;
      VH_propagate (VHTI_verify_signature(pub_key.c_str (),
                                          signed_data.c_str (),
                                          sig_node->str (). c_str (),
                                          &c_result),
                                          "SAFE_XML_TREE_CTOR");
      const std::string result (c_result);
      if (result.find ("Success") == result.npos)
         throw VH_exception (c_result);

      this->root ()-> erase ();
      xml_tree new_tree (signed_data);
      this->m_root = new_tree.root ()->deep_copy ();

      // TODO -- find a way to validate *as* we parse.  That would be
      // nicer than this, which parses a second time.
      VH_propagate (VHTI_validate (expected_root_element_name.c_str (),
                                   signed_data.c_str ()),
                    "INVALID_XML");
   }
   else
      VH_propagate (VHTI_validate (expected_root_element_name.c_str (),
                                   possibly_signed_xml.c_str ()),
                    "INVALID_XML");
}

}
