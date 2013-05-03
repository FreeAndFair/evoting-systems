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
 * @file PublicKey.h
 * Interface of the PublicKey class.
 */

#ifndef PUBLICKEY_H
#define PUBLICKEY_H

#include <string>
#include <boost/regex.hpp>

#include "Integer.h"
#include "common.h"
#include "ElgamalCiphertext.h"

namespace adder
{
    class Context;
    class PrivateKey;
    class Vote;

    /**
       \brief Elgamal public key.
     
       The main component of a public key is the value \f$h \in
       \langle g \rangle\f$.  To create a public key from scratch, you
       probably first want to generate a safe prime and then generate
       a key pair. As an example:

       \code 
       // Create a context object for random number generation.
       Context ctx;

       // Create an empty public key.
       PublicKey pub_key(&ctx); 

       // Generate a prime of length 1024 and a generator.
       pub_key.make_partial_key(1024);

       // Create the public key and return the corresponding private key.
       PrivateKey priv_key = pub_key.gen_key_pair();
       \endcode
     */
    class LIBADDER_API PublicKey {
    public:
        /**
           Default constructor. Use when you want to load a public key
           from a string.
           @param ctx the Context for random number generation.
        */
        PublicKey(Context* ctx = 0);

        /**
           Forms a public key with the given parameters.
           @param ctx the Context for random number generation.
           @param pz the modulus of the key.
           @param gz the generator of the key.
           @param hz the public key component of the key.
           @param fz the generator used for homomorphic encryption.
         */
        PublicKey(Context* ctx, Integer pz, Integer gz,
                  Integer hz, Integer fz);

        /**
           Returns a string representation of the key. The string is
           in the form \f$\texttt{p} \parallel p \parallel
           \texttt{g} \parallel g \parallel \texttt{h} \parallel h
           \parallel \texttt{f} \parallel f\f$,
           where \f$p, g, h, f\f$ are expressed in base 10.
        */
        std::string str() const;

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
        Integer get_h() const { return h; }

        /**
           Accessor method to retrieve the encryption generator.
        */
        Integer get_f() const { return f; }

        /**
           Encrypts a message by forming a ciphertext consisting of a
           power of base.  The ciphertext returned is of the form
           \f$\langle g^r, h^r f^{b^m} \rangle \f$, where \f$m\f$ is
           the message and \f$b\f$ is the base.
           @param message the message
           @param base the base
           @return the encryption of the base to the message power
        */
        ElgamalCiphertext encrypt(Integer message, Integer base);

        /**
           Encrypts a message as an additive homomorphic Elgamal
           ciphertext.  The ciphertext returned is of the form
           \f$\langle g^r, h^r f^m\rangle\f$, where \f$m\f$ is the
           message.
           @param message the message
           @return the encryption of the message
        */
        ElgamalCiphertext encrypt(Integer message);

        /**
           Encrypts a vote as a vector of ciphertexts.
           @param choices a boolean vector consisting of a yes/no
           choice for each candidate.
           @returns the vote
        */
        Vote encrypt(std::vector<bool> choices);

        /**
           Encrypts a polynomial value destined for an authority.  The
           ciphertext returned is of the form \f$\langle g^r, h^r
           (m+1)^2 \rangle\f$, where \f$m\f$ is the value of the source's
           polynomial evaluated at the ID of the destination.
           @param message the destination authority's ID.
           @return the encryption of the ID.
        */
        ElgamalCiphertext encrypt_poly(Integer message);

        /**
           Generates key parameters \f$p, g, f\f$ given a key length.
           This function generates a safe prime \f$p\f$.
           @param length the length of the key in bits.  That is,
           \f$p\f$ will be chosen to be a \e length - bit prime
           number.
        */
        void make_partial_key(int length);

        /**
           Generates key parameters \f$g, f\f$ given a prime \f$p\f$.
           @param pz the prime number
        */
        void make_partial_key(Integer pz);

        /**
           Loads the key from a string.
           @param key_string the string representation of a key.
           @exception Invalid_key the string was not well-formed.
           @see str
        */
        void from_str(std::string key_string);

        /**
           Generates the public key component of the key and returns
           the corresponding private key.  This is done by choosing
           \f$x \leftarrow_R \mathrm{Z}_q\f$, and setting \f$h
           = g^x\f$, and letting \f$x\f$ be the private key.
           @return the private key.
        */
        PrivateKey gen_key_pair();

    private:
        Integer p; /**< The prime modulus. */
        Integer g; /**< The generator. */
        Integer h; /**< The key component of the public key. */
        Integer f; /**< The generator used for homomorphic
                      encryption. */

        Context* context; /**< Context for random number generation. */

        Integer length; /**< The length of the key in bits. */
    };
}

#endif /* PUBLICKEY_H */
