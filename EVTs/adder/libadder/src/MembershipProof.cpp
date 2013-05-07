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
 * @file MembershipProof.cpp
 * Implementation of the MembershipProof class.
 */

#include <cstdlib>
#include <iostream>
#include <vector>

#include <boost/tokenizer.hpp>

#include "common.h"
#include "PublicKey.h"
#include "PrivateKey.h"
#include "MembershipProof.h"
#include "Integer.h"
#include "radix64.h"
#include "misc.h"
#include "exceptions.h"

using namespace std;

namespace adder 
{
    MembershipProof::MembershipProof()
    {
        p = Integer("0", 10);
    }

    void MembershipProof::compute(ElgamalCiphertext ciphertext,
                                  PublicKey pub_key,
                                  Integer value,
                                  vector<Integer> domain)
    {
        p = pub_key.get_p();
        Integer q = (p - 1) / 2;
        
        Integer g = Integer(pub_key.get_g(), p);
        Integer h = pub_key.get_h();
        Integer f = pub_key.get_f();
        
        Integer G = ciphertext.get_G();
        Integer H = ciphertext.get_H();
        Integer r = ciphertext.get_r();

        Integer t = Integer::random(q);

        stringstream hash_input;
        hash_input << g << h << G << H;

        unsigned int index_in_domain = 0;

        for (unsigned int i = 0; i < domain.size(); i++) {
            Integer y_i;
            Integer z_i;

            if (domain[i] == value) {
                c_vec.push_back(0);
                s_vec.push_back(0);
                y_i = g.pow(t);
                z_i = h.pow(t);
                index_in_domain = i;
            } else {
                c_vec.push_back(Integer::random(q));
                s_vec.push_back(Integer::random(q));

                y_i = g.pow(s_vec[i]) * G.pow(-c_vec[i]);
                z_i = h.pow(s_vec[i]) * (H / f.pow(domain[i])).pow(-c_vec[i]);
            }

            y_vec.push_back(y_i);
            z_vec.push_back(z_i);

            hash_input << y_i << z_i;
        }

        string hash = adder::sha1(hash_input.str());

        c = Integer(hash, q, 16);
        Integer real_c(c, q);

        for (unsigned int i = 0; i < c_vec.size(); i++) {
            real_c = real_c - c_vec[i];
        }

        s_vec[index_in_domain] = t + real_c * r;
        c_vec[index_in_domain] = real_c;
    }

    bool MembershipProof::verify(ElgamalCiphertext ciphertext, 
                                 PublicKey pub_key,
                                 vector<Integer> domain)
    {
        p = pub_key.get_p();
        Integer q = (p - 1) / 2;

        Integer g = pub_key.get_g();
        Integer h = pub_key.get_h();
        Integer f = pub_key.get_f();

        Integer G = ciphertext.get_G();
        Integer H = ciphertext.get_H();

        Integer c_choices("0", q, 10);

        std::stringstream hash_input;
        hash_input << g << h << G << H;

        for (unsigned int i = 0; i < c_vec.size(); i++) {
            c_choices = c_choices + c_vec[i];
            
            hash_input << g.pow(s_vec[i]) * G.pow(-c_vec[i])
                       << h.pow(s_vec[i]) * (H / f.pow(domain[i])).pow(-c_vec[i]);
        }
        
        std::string hash = adder::sha1(hash_input.str());
        Integer new_c(hash, q, 16);
        new_c = new_c % q;

        return (c_choices == new_c);
    }

    std::string MembershipProof::str() const
    {
        std::stringstream proof_input;
        std::vector<int>::size_type size;

        proof_input << 'p';
        proof_input << p;

        size = y_vec.size();

        for (std::vector<int>::size_type i = 0; i < size; i++) {
            proof_input << 'y';
            proof_input << y_vec[i];
        }

        size = z_vec.size();

        for (std::vector<int>::size_type i = 0; i < size; i++) {
            proof_input << 'z';
            proof_input << z_vec[i];
        }

        size = s_vec.size();

        for (std::vector<int>::size_type i = 0; i < size; i++) {
            proof_input << 's';
            proof_input << s_vec[i];
        }

        size = c_vec.size();

        for (std::vector<int>::size_type i = 0; i < size; i++) {
            proof_input << 'c';
            proof_input << c_vec[i];
        }

        return proof_input.str();
    }

    void MembershipProof::from_str(std::string proof_string)
    {
        boost::regex e("p(\\d+)((?:y\\d+)+)((?:z\\d+)+)((?:s\\d+)+)((?:c\\d+)+)");
        boost::smatch match;

        if (!boost::regex_match(proof_string, match, e)) {
            throw Invalid_proof("invalid membership proof: " + proof_string);
        } else {
            p = Integer(string(match[1].first, match[1].second));
            Integer q = (p - 1) / 2;
            string y_str(match[2].first, match[2].second);
            string z_str(match[3].first, match[3].second);
            string s_str(match[4].first, match[4].second);
            string c_str(match[5].first, match[5].second);

            typedef boost::tokenizer<boost::char_separator<char> > 
                tokenizer;
            tokenizer::iterator tok_iter;

            tokenizer tokens(y_str, boost::char_separator<char>("y"));
            for (tok_iter = tokens.begin();
                 tok_iter != tokens.end(); ++tok_iter) {
                y_vec.push_back(Integer(*tok_iter, p));
            }

            tokens.assign(z_str, boost::char_separator<char>("z"));
            for (tokenizer::iterator tok_iter = tokens.begin();
                 tok_iter != tokens.end(); ++tok_iter) {
                z_vec.push_back(Integer(*tok_iter, p));
            }


            tokens.assign(s_str, boost::char_separator<char>("s"));
            for (tokenizer::iterator tok_iter = tokens.begin();
                 tok_iter != tokens.end(); ++tok_iter) {
                s_vec.push_back(Integer(*tok_iter, q));
            }


            tokens.assign(c_str, boost::char_separator<char>("c"));
            for (tokenizer::iterator tok_iter = tokens.begin();
                 tok_iter != tokens.end(); ++tok_iter) {
                c_vec.push_back(Integer(*tok_iter, q));
            }
        }
    }
}
