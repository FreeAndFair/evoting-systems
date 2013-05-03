/* -*- Mode: C++; tab-width: 4; indent-tabs-mode: nil; c-basic-offset: 4 -*- */

/*  libadder - Cryptographic library for the Adder project.
    Copyright (C) 2004-2006  The Adder Team <adder@cse.uconn.edu>

    This program is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 2 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program; if not, write to the Free Software
    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

/**
 * @file VoteProof.h
 * Interface of the VoteProof class.
 */

#ifndef VOTEPROOF_H
#define VOTEPROOF_H

#include <string>
#include <vector>

#include "common.h"
#include "Integer.h"
#include "MembershipProof.h"

namespace adder
{
    /**
       \brief Proof of ciphertext vector vote validity.

       To show the validity of a vote, two statements must be proved:
       - Each ciphertext in the vote encrypts a 0-1 value.
       - The total number of 1s in the vote is within the required
       range.
    */
    class LIBADDER_API VoteProof {
    public:
        /**
           Default constructor.
        */
        VoteProof();

        /**
           Computes a proof of vote validity.
           
           First, this function proves that each ciphertext encrypts a
           0-1 value.  To do this, a proof is generated for each
           ciphertext in the vote, with a domain of \f$\{0, 1\}\f$.
           Then, all of the ciphertexts are multiplied together and a
           final proof is computed over the product of the
           ciphertexts, with a domain of \f$\{\mathit{minimum},\ldots,
           \mathit{maximum}\}\f$.
           
           @param vote the vote the proof will be computed over.
           @param pub_key the public key used to encrypt the vote.
           @param choices the vector of \em true/ \em false plaintext
           choices.
           @param minimum the minimum number of candidates required to
           be selected.
           @param maximum the maximum number of candidates required to be selected.
           @see MembershipProof::compute
        */
        void compute(Vote vote,
                     PublicKey pub_key,
                     std::vector<bool> choices,
                     Integer minimum,
                     Integer maximum);

        /**
           Verifies the proof.
           @param vote the vote the proof is computed over.
           @param pub_key the public key used to encrypt the vote.
           @param minimum the minimum number of candidates required to
           be selected.
           @param maximum the maximum number of candidates required to be
           selected.
           @return \b true if the proof is valid, \b false otherwise.
           @see MembershipProof::verify
        */
        bool verify(Vote vote, 
                    PublicKey pub_key,
                    Integer minimum,
                    Integer maximum);

        /**
           Returns a string representation of the proof. The string is
           in the form \f$\mathcal{P} \parallel P_1 \parallel \cdots
           \parallel P_c\f$, where \f$\mathcal{P}\f$ is the proof that
           the vote encrypts the proper number of choices, and
           \f$P_i\f$ is the proof that the \f$i\f$ th candidate is a 0
           or 1.
           @return the string representation of the proof.
           @see MembershipProof::str
        */
        std::string str() const;

        /**
           Loads the proof from a string.
           @param proof_string the string representation of a proof.
           @exception Invalid_proof the string was not well-formed.
           @see str, MembershipProof::from_str
        */
        void from_str(std::string proof_string);

    private:
        Integer p; /**< The modulus. */
        MembershipProof sum_proof; /**< The proof that the vote
                                      encrypts the proper number of candidates. */
        std::vector<MembershipProof> proof_vec; /**< The vector of 0-1
                                                   proofs. */
    };
}

#endif /* MEMBERSHIPPROOF_H */
