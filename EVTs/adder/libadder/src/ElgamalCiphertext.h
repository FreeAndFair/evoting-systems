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
 * @file ElgamalCiphertext.h
 * Interface of the ElgamalCiphertext class.
 */

#ifndef ELGAMALCIPHERTEXT_H
#define ELGAMALCIPHERTEXT_H

#include <string>

#include "common.h"
#include "Integer.h"

namespace adder
{
    /**
      \brief Additive homomorphic Elgamal ciphertext.
      
      An Elgamal ciphertext is represented as a pair \f$\langle G, H
      \rangle = \langle g^r,
      h^r f^m\rangle \in \mathrm{Z}_p \times \mathrm{Z}_p\f$.
      
      To form a ciphertext, you probably want to use the
      PublicKey::encrypt function.
     */
    class LIBADDER_API ElgamalCiphertext {
    public:
        /**
           Default constructor. Use this when you want to load a ciphertext
           from a string.
         */
        ElgamalCiphertext();

        /**
          Forms a ciphertext with the given parameters.
          @param G_z the first component of the ciphertext.
          @param H_z the second component of the ciphertext.
          @param p_z the modulus.
        */
        ElgamalCiphertext(Integer G_z, Integer H_z, Integer p_z);

        /**
          Forms a ciphertext with the given parameters.
          @param G_z the first component of the ciphertext.
          @param H_z the second component of the ciphertext.
          @param r_z the random component of the ciphertext.
          @param p_z the modulus.
        */
        ElgamalCiphertext(Integer G_z, Integer H_z, Integer r_z, Integer p_z);
       
        /**
           Returns a string representation of the ciphertext.  The
           string is in the form: \f$\texttt{p} \parallel p \parallel
           \texttt{G} \parallel G \parallel \texttt{H} \parallel H\f$,
           where \f$p, G, H\f$ are expressed in base 10.
        */
        std::string str() const;

        /**
           Returns a short hash of the ciphertext.  This is the first
           4 bytes of the SHA-1 of the ciphertext.
           @return the short hash.
        */
        std::string short_hash() const;

        /**
           Accessor method to retrieve the first component of the
           ciphertext.
           @return the first component of the ciphertext.
        */
        Integer get_G() const;

        /**
           Accessor method to retrieve the second component of the
           ciphertext.
           @return the second component of the ciphertext.
        */
        Integer get_H() const;

        /**
           Accessor method to retrieve the random component of the
           ciphertext.
           @return the random component of the ciphertext.
        */
        Integer get_r() const;

        /**
           Accessor method to retrieve the modulus component of the
           ciphertext.
           @return the modulus component of the ciphertext.
        */
        Integer get_p() const { return p; };

        /**
           Loads the ciphertext from a string.
           @param ciphertext_string the string representation of a
           ciphertext.
           @exception Invalid_ciphertext the string was not well-formed.
           @see str
        */
        void from_str(std::string ciphertext_string);

        /**
           Multiply two ciphertexts together.  This is accomplished by
           multiplying the two pairs component-wise.
           @param a the first ciphertext.
           @param b the second ciphertext.
           @return the product of the two ciphertexts.
        */
        friend ElgamalCiphertext operator*(const ElgamalCiphertext &a, 
                                           const ElgamalCiphertext &b);

    private:
        Integer G; /**< The first component of the ciphertext. */
        Integer H; /**< The second component of the ciphertext. */
        Integer r; /**< The random component of the ciphertext. */
        Integer p; /**< The modulus of the ciphertext. */
    };
}

#endif /* ELGAMALCIPHERTEXT_H */
