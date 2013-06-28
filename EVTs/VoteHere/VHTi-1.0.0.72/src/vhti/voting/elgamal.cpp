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
#include "support/support_internal.h"
#include "voting_internal.h"

namespace VHInternal {
void
encrypt_answer(const VHUtil::xml_node &answer,
               const BIGNUM *subgroup_generator,
               const BIGNUM *modulus,
               const BIGNUM *subgroup_order,
               const BIGNUM *ePublicKey,
               VHUtil::xml_tree::node *egp_destination,
               VHInternal::RS &rs)
{
   // An OpenSSL structure that holds BIGNUM temporary variables
   // used by library functions
   auto_BN_CTX ctx(BN_CTX_new());
   VH_nonzero(ctx, SSL_ERROR);

   auto_BN amark = xml2BN(answer->e(ANSWER_MARK));
                  
   // Generate alpha in Zq* to uniquely create the ElGamal Pair.
   // TODO: should we check that alpha is unique for each pair ?
   // (g^alpha, (h^alpha)*AnswerMark)

   auto_BN alpha; // The random alpha
   VHInternal::rand_range2(BN_value_one(), subgroup_order, rs, alpha);

   // A node for the ElGamalPair
   VHUtil::xml_tree::node *egp_node = egp_destination->new_element(EL_GAMAL_PAIR);

   auto_BN xxx; // g^alpha
   VHInternal::fixed_mod_exp(xxx,
                             subgroup_generator,
                             alpha,
                             modulus,
                             ctx);
   add_BN_element(egp_node, X_VALUE, xxx);
                  

   auto_BN yyy; // (h^alpha)*AnswerMark
   VHInternal::fixed_mod_exp(yyy,
                             ePublicKey,
                             alpha,
                             modulus,
                             ctx);
                  
   VH_nonzero (BN_mod_mul(yyy,
                          amark,
                          yyy,
                          modulus, ctx), SSL_ERROR);
   add_BN_element(egp_node, Y_VALUE, yyy);
}
}
