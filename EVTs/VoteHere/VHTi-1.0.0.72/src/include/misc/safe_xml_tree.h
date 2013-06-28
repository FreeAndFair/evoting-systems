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
#ifndef SAFE_XML_TREE_H
#define SAFE_XML_TREE_H
#pragma warning(disable: 4786)

#include <misc/xml_tree.h>
#include <string>

namespace VHUtil {
class safe_xml_tree : public VHUtil::xml_tree
{
 public:

   // Does two things depending on what the input string looks like.

   // If the input string does NOT look like "<SignedFoo>
   // ... <Signature>...</Signature></SignedFoo>", then we ignore
   // PUB_KEY, parse the XML, try to validate, and throw the usual
   // exception if possibly_signed_xml either
   //
   // 1) doesn't validate against g_dtd, or
   //
   // 2) its root element doesn't match EXPECTED_ROOT_ELEMENT_NAME.
   //
   // But if the input does look like the above, we first check the
   // signature against the characters, and throw a different
   // exception if that fails.  Then we start over with the signed
   // characters, in effect invisibly discarding the signature.

   // In the unlikely case that you
   //
   // 1) have something that has a signature
   //
   // 2) have no public key
   //
   // 3) do want XML validation
   //
   // pass the magic string "NO_SIGNATURE_CHECK" as the public key.
   
   safe_xml_tree (const std::string &possibly_signed_xml,
                  const std::string &expected_root_element_name,
                  const std::string &pub_key = "");
};

}

#endif
