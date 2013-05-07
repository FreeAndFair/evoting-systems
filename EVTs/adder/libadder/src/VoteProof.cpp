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
 * @file VoteProof.cpp
 * Implementation of the VoteProof class.
 */

#include <cstdlib>
#include <iostream>
#include <vector>

#include <boost/tokenizer.hpp>

#include "common.h"
#include "PublicKey.h"
#include "PrivateKey.h"
#include "VoteProof.h"
#include "Integer.h"
#include "radix64.h"
#include "misc.h"
#include "exceptions.h"

using namespace std;
using namespace boost;

namespace adder 
{
    VoteProof::VoteProof()
    {
        p = Integer("0", 10);
    }

    void VoteProof::compute(Vote vote, 
                            PublicKey pub_key,
                            vector<bool> choices,
                            Integer minimum,
                            Integer maximum)
    {
        p = pub_key.get_p();
        vector<ElgamalCiphertext> cipher_vec = vote.get_cipher_vec();

        vector<Integer> cipher_domain;
        cipher_domain.push_back(0);
        cipher_domain.push_back(1);

        ElgamalCiphertext sum_cipher(1, 1, p);
        Integer num_choices = 0;

        for (unsigned int i = 0; i < cipher_vec.size(); i++) {
            MembershipProof proof;
            proof.compute(cipher_vec[i], pub_key,
                          choices[i] ? 1 : 0, cipher_domain);
            proof_vec.push_back(proof);

            sum_cipher = sum_cipher * cipher_vec[i];

            num_choices = num_choices + (choices[i] ? 1 : 0);
        }

        vector<Integer> total_domain;
        for (Integer j = minimum; j <= maximum; j = j + 1) {
            total_domain.push_back(j);
        }

        MembershipProof proof;
        proof.compute(sum_cipher, pub_key,
                      num_choices, total_domain);

        sum_proof = proof;
    }

    bool VoteProof::verify(Vote vote,
                           PublicKey pub_key,
                           Integer minimum,
                           Integer maximum)
    {
        p = pub_key.get_p();

        vector<ElgamalCiphertext> cipher_vec = vote.get_cipher_vec();

        vector<Integer> cipher_domain;
        cipher_domain.push_back(0);
        cipher_domain.push_back(1);

        ElgamalCiphertext sum_cipher(1, 1, p);

        for (unsigned int i = 0; i < proof_vec.size(); i++) {
            if (!proof_vec[i].verify(cipher_vec[i],
                                     pub_key,
                                     cipher_domain)) {
                return false;
            }

            sum_cipher = sum_cipher * cipher_vec[i];
        }

        vector<Integer> total_domain;
        for (Integer j = minimum; j <= maximum; j = j + 1) {
            total_domain.push_back(j);
        }

        if (!sum_proof.verify(sum_cipher,
                              pub_key,
                              total_domain)) {
            return false;
        }

        return true;
    }

    std::string VoteProof::str() const
    {
        stringstream proof_ss;
        proof_ss << sum_proof.str();

        for (unsigned int i = 0; i < proof_vec.size(); i++) {
            proof_ss << " " << proof_vec[i].str();
        }

        return proof_ss.str();
    }

    void VoteProof::from_str(std::string proof_string)
    {
        tokenizer<> tok(proof_string);
        tokenizer<>::iterator t_iter;

        if (tok.begin() == tok.end()) {
            throw Invalid_proof("empty string");
        }

        t_iter = tok.begin();
        sum_proof.from_str(*t_iter);
        t_iter++;

        for (; t_iter != tok.end(); t_iter++) {
            MembershipProof proof;
            proof.from_str(*t_iter);
            proof_vec.push_back(proof);
        }
    }
}
