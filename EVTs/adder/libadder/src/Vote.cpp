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
 * @file Vote.cpp
 * Implementation of the Vote class.
 */

#include "common.h"
#include "Vote.h"
#include "radix64.h"
#include "exceptions.h"
#include "misc.h"

#include <iostream>
#include <boost/regex.hpp>
#include <boost/tokenizer.hpp>

using namespace boost;

namespace adder 
{
    Vote::Vote()
    {
    }

    Vote::Vote(std::vector<ElgamalCiphertext> cipher_vec)
    {
        this->cipher_vec = cipher_vec;
    }

    std::string Vote::str()
    {
        std::stringstream vote_stream;

        std::vector<ElgamalCiphertext>::iterator i;
        for (i = cipher_vec.begin(); i != cipher_vec.end(); i++) {
            vote_stream << i->str() << " ";
        }
 
        return vote_stream.str();
    }

    void Vote::from_str(std::string vote_string)
    {
        boost::regex e("(?:(p\\d+G\\d+H\\d+)\\s*)+");

        if (!boost::regex_match(vote_string, e)) {
            throw Invalid_vote("invalid vote: " + vote_string);
        } else {
            tokenizer<> tok(vote_string);
            tokenizer<>::iterator t_iter;
            
            std::vector<ElgamalCiphertext> vec;

            for (t_iter = tok.begin(); t_iter != tok.end(); t_iter++) {
                ElgamalCiphertext c;
                c.from_str(*t_iter);
                vec.push_back(c);
            }

            cipher_vec = vec;
        }
    }

    Vote operator*(const Vote &a, const Vote &b)
    {
        assert(a.cipher_vec.size() == b.cipher_vec.size());
        std::vector<ElgamalCiphertext> vec;

        for (unsigned int i = 0; i < a.cipher_vec.size(); i++) {
            vec.push_back(a.cipher_vec[i] * b.cipher_vec[i]);
        }

        return Vote(vec);
    }
}
