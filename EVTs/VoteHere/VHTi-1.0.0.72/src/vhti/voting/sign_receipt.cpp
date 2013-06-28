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

#include "vhti/sign_receipt.h"
#include "vhti/sign.h"
#include <support/internal_error.h>
#include <support/bignum.h>
#include <misc/safe_xml_tree.h>
#include <string>
#include <sstream>

int
VHTI_sign_receipt (VoteReceiptData vote_receipt_data,
                   GeneralPurposePrivateKey receipt_signing_key,
                   SignedVoteReceiptData * vote_receipt)
{
   // Assume success until told otherwise
   int result = 0;
   *vote_receipt = NULL;

   try
   {
      result = (::VHTI_validate(VOTE_RECEIPT_DATA, vote_receipt_data));
      
      if (result != 0) throw VH_exception("VALIDATION_FAILURE");

      VH_propagate (VHTI_sign_xml (receipt_signing_key,
                                   vote_receipt_data,
                                   vote_receipt),
         "SIGNING_XML");
   }
   catch (const VHUtil::Exception & e)
   {
      VHTI_set_last_error(e);
      result = e.getResultNo();
   }
   return result;
}
