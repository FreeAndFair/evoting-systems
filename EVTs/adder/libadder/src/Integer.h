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
 * @file Integer.h
 * Interface of the Integer class.
 */

#ifndef INTEGER_H
#define INTEGER_H

#include <string>
#include <iostream>

#include "common.h"
#include "time.h"
#include "Context.h"

namespace adder
{
    /**
     * Class to represent a big integer.
     */
    class LIBADDER_API Integer {
        static Context ctx;
        
    public:
        Integer();
        Integer(const Integer &a);
        Integer(unsigned int i);
        Integer(const std::string &s, int base = 10);
        explicit Integer(mpz_srcptr a);
        explicit Integer(mpz_srcptr a, mpz_srcptr m);
        Integer(const Integer &a, const Integer &m);
        Integer(const std::string &s, Integer &m, int base = 10);
        Integer(unsigned int i, unsigned int m);

        ~Integer();

        bool divisible(Integer &b) const;

        void set_str(const std::string &s, Integer &m, int base = 10);

        Integer get_value();
        Integer get_modulus();

        static Integer random(Integer i);
        static Integer random(unsigned int i);
        static Integer random(std::string s);
        static Integer random(mpz_srcptr z);
        static Integer gen_safe_prime(int length);

        std::string str(int base = 10) const;

        Integer pow(Integer e);

        /* Overloaded assignment operators. */
        void operator=(Integer a);
        void operator=(unsigned int i);
        void operator=(std::string s);
        void operator=(mpz_t a);

        /* Overloaded arithmetic operators. */
        Integer operator-() const;
        friend Integer operator+(const Integer &a, const Integer &b);
        friend Integer LIBADDER_API operator-(const Integer &a, const Integer &b);
        friend Integer operator*(const Integer &a, const Integer &b);
        friend Integer LIBADDER_API operator/(const Integer &a, const Integer &b);
        friend Integer operator%(const Integer &a, const Integer &b);

        /* Overloaded iostream operators. */
        friend std::ostream &operator<<(std::ostream &o, const Integer &a);

        /* Overloaded comparison operators. */
        friend bool operator==(const Integer &a, const Integer &b);
        friend bool operator!=(const Integer &a, const Integer &b);
        friend bool operator>=(const Integer &a, const Integer &b);
        friend bool operator>(const Integer &a, const Integer &b);
        friend bool operator<=(const Integer &a, const Integer &b);
        friend bool operator<(const Integer &a, const Integer &b);
        
    private:
        mpz_t value;
        mpz_t modulus;

    };
}

#endif /* INTEGER_H */
