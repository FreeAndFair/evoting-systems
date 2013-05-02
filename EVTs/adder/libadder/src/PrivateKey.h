/* -*- Mode: C++; tab-width: 4; indent-tabs-mode: nil; c-basic-offset: 4 -*- */

/*  libadder - Cryptographic library for the Adder project.
    Copyright (C) 2004  The Adder Team <adder@cse.uconn.edu>

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
 * @file PrivateKey.h
 * Interface of the PrivateKey class.
 */

#ifndef PRIVATEKEY_H
#define PRIVATEKEY_H

#include <string>
#include <vector>

#include "common.h"
#include "Integer.h"
#include "Vote.h"

namespace adder
{
    class Vote;

    /**
       \brief Elgamal private key.
       
       The main component of a public key is the value \f$x \in
       \mathrm{Z}_q \f$.
    */
    class LIBADDER_API PrivateKey {
    public:
        /**
           Default constructor. Use when you want to load a private key
           from a string.
        */
        PrivateKey();

        /**
           Forms a private key with the given parameters.
           @param pz the modulus of the key.
           @param gz the generator of the key.
           @param xz the private key component of the key.
           @param fz the generator used for homomorphic encryption.
        */
        PrivateKey(Integer pz, Integer gz, Integer xz, Integer fz);

        /**
           Accessor method to retrieve the key modulus.
        */
        Integer get_p() const { return p; }

        /**
           Accessor method to retrieve the key generator.
        */
        Integer get_g() const { return g; }

        /**
           Accessor method to retrieve the key component.
        */
        Integer get_x() const { return x; }

        /**
           Accessor method to retrieve the encryption generator.
        */
        Integer get_f() const { return f; }

        /**
           Returns a string representation of the key. The string is
           in the form \f$\texttt{p} \parallel p \parallel
           \texttt{g} \parallel g \parallel \texttt{x} \parallel x
           \parallel \texttt{f} \parallel f\f$,
           where \f$p, g, x, f\f$ are expressed in base 10.
        */
        std::string str() const;
        
        /**
           Computes the authority's partial decryption of a sum. The
           \f$i\f$th component of the partial decryption is computed
           as \f$G_i ^ x\f$, where \f$G_i\f$ is the first component of
           the \f$i\f$ th ciphertext in the sum.

           @param vote the vector of ciphertexts representing the
           election total.
           @return the partial decryption as a vector of integers.
        */
        std::vector<Integer> partial_decrypt(Vote vote);

        /**
           Computes the final private key for each authority.
           @param poly_list the list of polynomial data for the
           authority.
           @return the authority's final private key.
        */
        PrivateKey get_final_priv_key(std::vector<ElgamalCiphertext> poly_list);
        
        /**
           Loads the key from a string.
           @param key_string the string representation of a key.
           @exception Invalid_key the string was not well-formed.
           @see str
        */
        void from_str(std::string key_string);

    private:
        Integer p; /**< The prime modulus. */
        Integer g; /**< The generator. */
        Integer x; /**< The key component of the private key. */
        Integer f; /**< The generator used for homomorphic
                      encryption. */
    };
}

#endif /* PRIVATEKEY_H */
