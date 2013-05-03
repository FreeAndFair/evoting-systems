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
 * @file ElgamalCiphertext.cpp
 * Implementation of the ElgamalCiphertext class.
 */

#include "common.h"
#include "ElgamalCiphertext.h"
#include "radix64.h"
#include "exceptions.h"
#include "misc.h"

#include <iostream>

#include <boost/regex.hpp>

namespace adder 
{
    ElgamalCiphertext::ElgamalCiphertext()
    {
    }

    ElgamalCiphertext::ElgamalCiphertext(Integer G_z, Integer H_z, Integer p_z)
    {
        G = Integer(G_z, p_z);
        H = Integer(H_z, p_z);
        p = p_z;
    }

    ElgamalCiphertext::ElgamalCiphertext(Integer G_z, Integer H_z, Integer r_z, Integer p_z)
    {
        G = Integer(G_z, p_z);
        H = Integer(H_z, p_z);
        r = r_z;
        p = p_z;
    }

    std::string ElgamalCiphertext::str() const
    {
        std::stringstream ElgamalCiphertext_stream;
        ElgamalCiphertext_stream << "p" << p.str() << "G" << G.str() << "H" << H.str();
        std::string ElgamalCiphertext_string = ElgamalCiphertext_stream.str();

        return ElgamalCiphertext_string;
    }

    std::string ElgamalCiphertext::short_hash() const
    {
        std::string long_hash = sha1(str());
        std::string short_hash = long_hash.substr(0, 5);
        return short_hash;
    }
    
    Integer ElgamalCiphertext::get_G() const
    {
        return G;
    }

    Integer ElgamalCiphertext::get_H() const
    {
        return H;
    }

    Integer ElgamalCiphertext::get_r() const
    {
        return r;
    }

    void ElgamalCiphertext::from_str(std::string ciphertext_string)
    {
        boost::regex e("p(\\d+)G(\\d+)H(\\d+)");
        boost::smatch match;
        if (!boost::regex_match(ciphertext_string, match, e)) {
            throw Invalid_ciphertext("invalid ElgamalCiphertext: " + 
                                     ciphertext_string);
        } else {
            p = Integer(std::string(match[1].first, match[1].second));
            G = Integer(std::string(match[2].first, match[2].second), p);
            H = Integer(std::string(match[3].first, match[3].second), p);
        }
    }

    ElgamalCiphertext operator*(const ElgamalCiphertext &a,
                                const ElgamalCiphertext &b)
    {
        Integer p = a.get_p();
        Integer G = a.get_G() * b.get_G();
        Integer H = a.get_H() * b.get_H();
        Integer r = a.get_r() + b.get_r();
        
        return ElgamalCiphertext(G, H, r, p);
    }
}
