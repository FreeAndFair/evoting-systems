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
 * @file PublicKey.cpp
 * Implementation of the PublicKey class.
 */

#include <cstdlib>
#include <iostream>

#include "common.h"
#include "PublicKey.h"
#include "PrivateKey.h"
#include "radix64.h"
#include "misc.h"
#include "exceptions.h"
#include "Integer.h"

namespace adder 
{
    PublicKey::PublicKey(Context* ctx)
    {
        context = ctx;
    }

    PublicKey::PublicKey(Context* ctx, Integer pz, Integer gz, 
                         Integer hz, Integer fz)
    {
        context = ctx;
        
        p = pz;
        g = gz;
        h = hz;
        f = fz;
    }

    std::string PublicKey::str() const
    {         
        std::stringstream key_ss;

        key_ss << 'p' << p.str() << 'g' << g.str() 
               << 'h' << h.str() << 'f' << f.str();
        
        return key_ss.str();
    }
 
    void PublicKey::make_partial_key(Integer p_z)
    {
        Integer t;
        Integer q;
        Integer a;

        p = p_z;

        /* Find a value t such that t is in (1, p - 1). */
        do {
            t = Integer::random(p);
        } while (t <= 1);

        /* Set g to be t^2 (mod p), after which g will be a generator
         * of the prime order group QR_p. */
        g = t.pow(2);

        /* Set q to be the order of QR_p. */
        q = (p - 1) / 2;

        /* Find a value a such that a is in (0, q). */
        do {
            a = Integer::random(q);
        } while (a <= 1);

        /* Set f to be g^a (mod p). */
        f = g.pow(a);
    }

    void PublicKey::make_partial_key(int length)
    {
        /* Set p to be a random prime length-bit number. */
        p = Integer::gen_safe_prime(length);

        make_partial_key(p);
    }

    PrivateKey PublicKey::gen_key_pair()
    {
        Integer q = (p - 1) / 2;
        Integer x = Integer::random(q);

        h = g.pow(x);

        PrivateKey priv_key(p, g, x, f);

        return priv_key;
    }

    void PublicKey::from_str(std::string key_string)
    {
        boost::regex e("p(\\d+)g(\\d+)h(\\d+)f(\\d+)");
        boost::smatch match;
        if (!boost::regex_match(key_string, match, e)) {
            throw Invalid_key("invalid public key: " + key_string);
        } else {
            p = Integer(std::string(match[1].first, match[1].second));
            g = Integer(std::string(match[2].first, match[2].second), p);
            h = Integer(std::string(match[3].first, match[3].second), p);
            f = Integer(std::string(match[4].first, match[4].second), p);
        }
    }

    ElgamalCiphertext PublicKey::encrypt(adder::Integer choice, Integer base)
    {   
        Integer q = (p - 1) / 2;
        Integer r = Integer::random(q);
        Integer message = base.pow(choice);
        Integer G = g.pow(r);
        Integer H = h.pow(r) * f.pow(message);
        
        ElgamalCiphertext cipher(G, H, r, p);
        
        return cipher;
    }

    ElgamalCiphertext PublicKey::encrypt(adder::Integer message)
    {
        Integer q = (p - 1) / 2;
        Integer r = Integer::random(q);
        Integer G = g.pow(r);
        Integer H = h.pow(r) * f.pow(message);

        ElgamalCiphertext cipher(G, H, r, p);

        return cipher;
    }

    Vote PublicKey::encrypt(std::vector<bool> choices)
    {
        std::vector<ElgamalCiphertext> vote_vec;

        std::vector<bool>::iterator i;
        for (i = choices.begin(); i != choices.end(); i++) {
            Integer choice = *i ? Integer("1", 10) : Integer("0", 10);
            vote_vec.push_back(encrypt(choice));
        }
        
        return Vote(vote_vec);
    }

    ElgamalCiphertext PublicKey::encrypt_poly(Integer message)
    {
        Integer q = (p - 1) / 2;
        Integer r = Integer::random(q);
        Integer G = g.pow(r);
        Integer H = h.pow(r) * Integer(message + 1, p).pow(2);
       
        ElgamalCiphertext cipher(G, H, p);

        return cipher;
    }
}
