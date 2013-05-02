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
 * @file Polynomial.h
 * Interface of the Polynomial class.
 */

#ifndef POLYNOMIAL_H
#define POLYNOMIAL_H

#include <string>
#include <sstream>
#include <vector>

#include "common.h"
#include "Integer.h"

namespace adder
{
    class Context;

    /**
     * Class to represent a polynomial.  This class contains a vector
     * of coefficients, as well as functions to generate random
     * coefficients and calculate Lagrange coefficients.
     */
    class LIBADDER_API Polynomial {
    public:
        Polynomial(Context* c);
        Polynomial(Context* c, Integer pz, Integer gz, Integer fz);
        ~Polynomial();

        std::string str() const;
        std::string armor() const;
        void load_from_armor(std::string poly_string);
        Integer get_p() const;
        Integer get_g() const;
        Integer get_f() const;
        void gen_rand_coeffs(Integer d, Integer p);
        Integer evaluate(Integer x) const;
        Integer get_degree() const;
#if _MSC_VER
#pragma warning(push)
#pragma warning(disable: 4251)
#endif // _MSC_VER

        std::vector<Integer> coeffs;

#if _MSC_VER
#pragma warning(pop)
#endif // _MSC_VER

        static std::vector<Integer> lagrange(std::vector<Integer> auth_indx, Integer p);

    private:
        int degree;
        Integer p;
        Integer g;
        Integer f;

        Context* context;
    };
}

#endif /* POLYNOMIAL_H */
