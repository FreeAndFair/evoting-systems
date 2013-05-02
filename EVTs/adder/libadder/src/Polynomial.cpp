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
 * @file Polynomial.cpp
 * Implementation of the Polynomial class.
 */

#include <cstdlib>
#include <iostream>
#include <cmath>

#include "common.h"
#include "misc.h"
#include "radix64.h"
#include "Polynomial.h"
#include "exceptions.h"

namespace adder 
{
    /**
     * Constructor.  Takes a Context object and initializes the private members.
     * @param c pointer to a Context.
     */
    Polynomial::Polynomial(Context* c)
    {
        context = c;
        degree = 0;
    }

    Polynomial::~Polynomial()
    {

    }

    /**
     * Constructor.  This version of the constructors allows you to
     * initalizes private members. 
     * @param c pointer to a Context.
     * @param pz Integer of the p value.
     * @param gz Integer of the g value.
     * @param fz Integer of the f value.
     */
    Polynomial::Polynomial(Context* c, Integer pz, Integer gz, 
                           Integer fz)
    {
        context = c;

        p = pz;
        g = gz;
        f = fz;
        degree = 0;
    }

    /**
     * Returns a string representation of the polynomial.
     * @return a string representation of the polynomial.
     */
    std::string Polynomial::str() const
    {         
        std::string poly_string;
        std::vector<Integer>::size_type size = coeffs.size();

        poly_string = poly_string + 'p' + p.str();
        poly_string = poly_string + 'g' + g.str();
        poly_string = poly_string + 'f' + f.str();
        
        for (std::vector<Integer>::size_type i = 0; i < size; i++) {
            poly_string = poly_string + ' ';
            poly_string = poly_string + coeffs[i].str();
        }

        return poly_string;
    }

    /**
     * Returns an ASCII-armored representation of the polynomial. This
     * is currently disabled, as ASCII-armoring is broken. 
     * @return an ASCII-armored representation of the polynomial.
     */
    std::string Polynomial::armor() const
    {
        std::string poly_string = str();

#ifdef ARMOR
        key_string = encode_radix_64(poly_string);   /* encode message */
        key_string = en_armor(key_string, "PUBLIC KEY");  /* wrap message */
#endif

        return poly_string;
    }
    
    /**
     * Initializes the polynomial to the polynomial described by an
     * ASCII-armored string. Currently, since ASCII-armoring is
     * broken, this accepts a string in the native format. 
     * @param poly_string a string representation of the polynomial. 
     */
    void Polynomial::load_from_armor(std::string poly_string) // FIXME: allows extra stff after the polynomial
    {
                
        std::stringstream ps;
        std::stringstream gs;
        std::stringstream fs;
        std::vector<std::string> tokens;
        std::string pgf;  
        bool is_valid;
        size_t size;

#ifdef ARMOR
        try {
            key_string = de_armor(key_string, "PUBLIC KEY");  /* Remove wrapping. */
            key_string = decode_radix_64(poly_string);  /* Remove encoding.  */
        } catch (Invalid_armor e) {
            throw Invalid_polynomial("invalid polynomial: " + e.msg());
        } catch (Invalid_encoding e) {
            throw Invalid_polynomial("invalid polynomial: " + e.msg());
        }
#endif

        tokens = tokenize(poly_string);
        
        pgf = tokens[0];
        tokens.erase(tokens.begin());
        
        is_valid = false;
        
        size = pgf.length();

        size_t i = 0;

        if (i < size && pgf[i] == 'p') {
            i++;
            while (i < size && isdigit(pgf[i])) {
                ps << pgf[i];
                i++;
            }
            if (i < size && pgf[i] == 'g') {
                i++;
                while (i < size && isdigit(pgf[i])) {
                    gs << pgf[i];
                    i++;
                }
                if (i < size && pgf[i] == 'f') {
                    i++;
                    while (i < size && isdigit(pgf[i])) {
                        fs << pgf[i];
                        i++;
                    }
                    is_valid = true;
                }
            }
        }
        if (is_valid == false) {
            /* Throw error code to caller. */
            throw Invalid_polynomial("invalid polynomial");
        }

        p = Integer(ps.str());
        g = Integer(gs.str(), p);
        f = Integer(fs.str(), p);

        for (unsigned int i = 0; i < tokens.size(); i++) {
            coeffs.push_back(Integer(tokens[i])); // XXX: should we have a modulus here?
            degree++; // XXX: degree matches size of coeffs already
        }
    }

    /**
     * Returns the p value.
     * @return the p value.
     */
    Integer Polynomial::get_p() const
    {
        return p;
    }

    /**
     * Returns the g value.
     * @return the g value.
     */
    Integer Polynomial::get_g() const
    {
        return g;
    }

    /**
     * Returns the f value.
     * @return the f value.
     */
    Integer Polynomial::get_f() const
    {
        return f;
    }

    /**
     * Generates a random set of coefficients for the
     * polynomial. Coefficients are chosen from Z_q, 
     * where q = (p - 1) / 2.  
     * @param d the degree of the polynomial.  
     * @param p the prime modulus.
     */    
    void Polynomial::gen_rand_coeffs(Integer d, Integer p) // XXX: we already have p as a member
    {
        Integer q = (p - 1) / 2;
        for (int i = 0; i <= d; i++) {
            coeffs.push_back(Integer::random(q));
            degree++;
        }

        degree--;
    }

    /**
     * Evaluates the polynomial at a particular point.
     * @param x the point to evaluate at.
     * @return the string representation of the polynomial at x.
     */
    Integer Polynomial::evaluate(Integer x) const
    {
        Integer q = (p - 1) / 2;

        Integer eval_sum("0", q, 10);

        for (std::vector<Integer>::size_type i = 0; i < coeffs.size(); i++) {
            eval_sum = eval_sum + (coeffs[(int)i] * Integer(x, q).pow(int(i)));
        }

        return eval_sum;
    }

    /**
     * Returns the get of the polynomial.
     * @return the degree of the polynomial.
     */
    Integer Polynomial::get_degree() const
    {
        return Integer(degree, 0);
    }

    /**
     * Returns a vector of Lagrange coefficients.
     * @param auth_indx the list of input coefficients.
     * @param p the prime
     * @return the list of Lagrange coefficients.
     */
    std::vector<Integer> Polynomial::lagrange(std::vector<Integer> auth_indx, Integer p)
    {
        Integer q = (p - 1) / 2; // XXX: we already have p as a member
        
        std::vector<Integer> lagrange_coeffs;

        for (unsigned int i = 0; i < auth_indx.size(); i++) {
            /* Get the numerator. */
            Integer numerator("1", q, 10);

            for (unsigned int j = 0; j < auth_indx.size(); j++) {
                if (auth_indx[i] != auth_indx[j]) {
                    numerator = numerator * (q - auth_indx[j]);
                }
            }

            /* Get the denominator. */
            Integer denominator("1", q, 10);

            for (unsigned int j = 0; j < auth_indx.size(); j++) {
                if (auth_indx[i] != auth_indx[j]) {
                    denominator = denominator * (Integer(auth_indx[i], q) - Integer(auth_indx[j], q));
                }
            }

            lagrange_coeffs.push_back(numerator / denominator);
        }

        return lagrange_coeffs;
    }
}
