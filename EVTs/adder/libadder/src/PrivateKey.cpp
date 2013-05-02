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
 * @file PrivateKey.cpp
 * Implementation of the PrivateKey class.
 */

#include <cstdlib>
#include <iostream>
#include <boost/regex.hpp>
#include <vector>

#include "common.h"
#include "radix64.h"
#include "exceptions.h"
#include "misc.h"
#include "PrivateKey.h"

using namespace std;

namespace adder 
{
    PrivateKey::PrivateKey()
    {
    }

    PrivateKey::PrivateKey(Integer pz, Integer gz, Integer xz, Integer fz)
    {
        p = pz;
        g = gz;
        x = xz;
        f = fz;
    }

    std::string PrivateKey::str() const
    {         
        std::stringstream key_ss;

        key_ss << 'p' << p
               << 'g' << g
               << 'x' << x
               << 'f' << f;
        
        return key_ss.str();
    }

    std::vector<Integer> PrivateKey::partial_decrypt(Vote vote)
    {
        std::vector<ElgamalCiphertext> cipher_vec = vote.get_cipher_vec();
        std::vector<Integer> result_vec;

        std::vector<ElgamalCiphertext>::iterator i;

        for (i = cipher_vec.begin(); i != cipher_vec.end(); i++) {
            Integer G = i->get_G();
            result_vec.push_back(G.pow(x));
        }
        
        return result_vec;
    }

    void PrivateKey::from_str(std::string key_string)
    {
        boost::regex e("p(\\d+)g(\\d+)x(\\d+)f(\\d+)");
        boost::smatch match;
        if (!boost::regex_match(key_string, match, e)) {
            throw Invalid_key("invalid private key: " + key_string);
        } else {
            p = Integer(std::string(match[1].first, match[1].second));
            g = Integer(std::string(match[2].first, match[2].second), p);

            Integer q = (p - 1) / 2;
            x = Integer(std::string(match[3].first, match[3].second), q);
            f = Integer(std::string(match[4].first, match[4].second), p);
        }
    }

    PrivateKey PrivateKey::get_final_priv_key(std::vector<ElgamalCiphertext> 
                                              poly_list)
    {
        Integer q = (p - 1) / 2;
        Integer total("0", q, 10);
        
        for (unsigned int i = 0; i < poly_list.size(); i++) {
            Integer e_L = poly_list[i].get_G();
            Integer e_R = poly_list[i].get_H();

            Integer product = e_L.pow(-x) * e_R;

            Integer pos_inverse = product.pow((q + 1) / 2);
            Integer neg_inverse = -pos_inverse;
            Integer inverse = 
                (pos_inverse < neg_inverse) ? pos_inverse : neg_inverse;
            inverse = inverse - 1;

            total = total + inverse;
        }

        PrivateKey priv_key(p, g, total, f);

        return priv_key;
    }
}
