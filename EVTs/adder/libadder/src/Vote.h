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
 * @file Vote.h
 * Interface of the Vote class.
 */

#ifndef VOTE_H
#define VOTE_H

#include <string>
#include <vector>

#include "common.h"
#include "Integer.h"
#include "ElgamalCiphertext.h"

namespace adder
{
    /**
       \brief Ciphertext-vector vote.
       
       A vote consists of a vector of ciphertexts. Each ciphertext
       represents the encryption of a yes/no for one candidate.
    */
    class LIBADDER_API Vote {
    public:
        /**
           Default constructor. Use when you want to load a vote from
           a string.
        */
        Vote();
        
        /**
           Initializes a vote from a vector of ciphertexts.
        */
        Vote(std::vector<ElgamalCiphertext>);

        /**
           Returns a string representation of the vote.  This is
           represented a list of ElgamalCiphertext strings, separated by
           whitespace.
           @return the string representation of the vote.
           @see ElgamalCiphertext::str
         */
        std::string str();

        /**
           Load the vote from a string.
           @param vote_string the string representation of a vote.
           @exception Invalid_vote the string was not well-formed.
           @see str
        */
        void from_str(std::string vote_string);

        /**
           Multiplies two votes component-wise.
           @param a the first vote.
           @param b the second vote.
           @return the product of the two votes.
        */
        friend Vote operator*(const Vote &a, const Vote &b);

        /**
           Accessor function to retrieve the cipher_vec.
           @return the vector of ciphertexts.
        */
        std::vector<ElgamalCiphertext> get_cipher_vec() const { return cipher_vec; }

    private:
        std::vector<ElgamalCiphertext> cipher_vec; /**< The vector of
                                                      ciphertexts. */
    };
}

#endif /* VOTE_H */
