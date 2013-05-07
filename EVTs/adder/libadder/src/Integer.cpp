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
 * @file Integer.cpp
 * Implementation of the Integer class.
 */

#include "Integer.h"
#include <iostream>

namespace adder
{
    Context Integer::ctx(true);

    Integer::Integer()
    {
        mpz_init(value);
        mpz_init_set_ui(modulus, 0);
    }

    Integer::Integer(const Integer& a)
    {
        mpz_init_set(value, a.value);
        mpz_init_set(modulus, a.modulus);
    }

    Integer::Integer(unsigned int i)
    {
        mpz_init_set_ui(value, i);
        mpz_init_set_ui(modulus, 0);
    }

    Integer::Integer(const std::string& s, int base)
    {
        mpz_init_set_str(value, s.c_str(), base);
        mpz_init_set_ui(modulus, 0);
    }

    Integer::Integer(mpz_srcptr a)
    {
        mpz_init_set(value, a);
        mpz_init_set(modulus, 0);
    }

    Integer::Integer(mpz_srcptr a, mpz_srcptr m)
    {
        mpz_init_set(value, a);
        mpz_init_set(modulus, m);
        mpz_mod(value, value, modulus);
    }

    Integer::Integer(const Integer& a, const Integer& m)
    {
        mpz_init_set(value, a.value);
        mpz_init_set(modulus, m.value);
        mpz_mod(value, value, modulus);
    }

    Integer::Integer(const std::string& s, Integer &m, int base)
    {
        set_str(s, m, base);
    }

    Integer::Integer(unsigned int i, unsigned int m)
    {
        mpz_init_set_ui(value, i);
        mpz_init_set_ui(modulus, m);
        mpz_mod(value, value, modulus);
    }

    Integer::~Integer()
    {
        mpz_clear(value);
        mpz_clear(modulus);
    }

    bool Integer::divisible(Integer &b) const
    {
        mpz_t b_z;
        mpz_init_set_str(b_z, b.str().c_str(), 0);

        int result = mpz_divisible_p(value, b_z);
        mpz_clear(b_z);

        return result ? true : false;
    }

    void Integer::set_str(const std::string &s, Integer &m, int base)
    {
        mpz_init_set_str(value, s.c_str(), base);
        mpz_init_set_str(modulus, m.str().c_str(), 10);

        if (mpz_cmp_ui(modulus, 0) != 0) {
            mpz_mod(value, value, modulus);
        }
    }

    Integer Integer::get_value()
    {
        char* vs = mpz_get_str(0, 10, value);

        Integer v(vs, 10);

        free(vs);

        return v;
    }

    Integer Integer::get_modulus()
    {
        char* ms = mpz_get_str(0, 10, modulus);

        Integer m(ms, 10);

        free(ms);

        return m;
    }

    Integer Integer::random(Integer i)
    {
        Integer c;

        mpz_set(c.modulus, i.value);
        
        mpz_urandomm(c.value, *ctx.get_state(), i.value);
        
        mpz_mod(c.value, c.value, c.modulus);
        
        return c;
    }

    Integer Integer::random(unsigned int i)
    {
        Integer c(i);

        return random(c);
    }

    Integer Integer::random(std::string s)
    {
        Integer c;

        mpz_set_str(c.value, s.c_str(), 10);

        return random(c);
    }

    Integer Integer::random(mpz_srcptr z)
    {
        Integer c(z);

        return random(c);
    }

    Integer Integer::gen_safe_prime(int length)
    {
        mpz_t p;
        mpz_t diff;
        mpz_t quotient;

        mpz_init2(p, length);
        mpz_init(diff);
        mpz_init(quotient);

        /* Loop until we know that p is a safe prime. */
        do {
            do {
                mpz_urandomb(p, *ctx.get_state(), length); /* Set p to be a random number. */
                mpz_setbit(p, length - 1); /* Set MSB to make p length bits long. */ // XXX: Line above specifies length
                mpz_setbit(p, 0); /* Set LSB to make p odd. */
            } while (!mpz_probab_prime_p(p, 10));
            
            mpz_sub_ui(diff, p, 1);
            mpz_divexact_ui(quotient, diff, 2);
        } while (!mpz_probab_prime_p(quotient, 10));
        
        Integer p_int(mpz_get_str(0, 10, p));
        
        mpz_clear(diff);
        mpz_clear(quotient);
        mpz_clear(p);
        
        return p_int;
    }

    std::string Integer::str(int base) const
    {
        char *cs = mpz_get_str(0, base, value);

        std::string s(cs);

        free(cs);

        return s;
    }

    void Integer::operator=(Integer a)
    {
        mpz_set(value, a.value);
        mpz_set(modulus, a.modulus);
    }

    void Integer::operator=(unsigned int i)
    {
        mpz_set_ui(value, i);
    }

    void Integer::operator=(std::string s)
    {
        mpz_set_str(value, s.c_str(), 10);
    }

    void Integer::operator=(mpz_t a)
    {
        mpz_set(value, a);
    }

    Integer Integer::operator-() const
    {
        Integer c; 

        mpz_sub(c.value, modulus, value);

        return c;
    }

    Integer operator+(const Integer& a, const Integer& b)
    {
        Integer c;

        mpz_set(c.modulus, a.modulus);

        mpz_add(c.value, a.value, b.value);

        if (mpz_cmp_ui(a.modulus, 0)) {
            mpz_mod(c.value, c.value, c.modulus);
        }

        return c;
    }

    Integer operator-(const Integer& a, const Integer& b)
    {
        Integer c;

        mpz_set(c.modulus, a.modulus);

        if (mpz_cmp_ui(a.modulus, 0)) {
            mpz_add(c.value, a.value, (-b).value);
        } else {
            mpz_sub(c.value, a.value, b.value);
        }

        return c;
    }

    Integer operator*(const Integer& a, const Integer& b)
    {
        Integer c;

        mpz_set(c.modulus, a.modulus);

        mpz_mul(c.value, a.value, b.value);

        if (mpz_cmp_ui(a.modulus, 0)) {
            mpz_mod(c.value, c.value, c.modulus);
        }

        return c;
    }

    Integer operator/(const Integer& a, const Integer& b)
    {
        Integer c;

        mpz_set(c.modulus, a.modulus);

        if (mpz_cmp_ui(a.modulus, 0)) {
            Integer b_inv;
            mpz_invert(b_inv.value, b.value, a.modulus);
            mpz_mul(c.value, a.value, b_inv.value);
            mpz_mod(c.value, c.value, c.modulus);
        } else {
            mpz_tdiv_q(c.value, a.value, b.value);
        }

        return c;
    }

    Integer operator%(const Integer& a, const Integer& b)
    {
        Integer c;

        mpz_set(c.modulus, a.modulus);

        mpz_mod(c.value, a.value, b.value);

        return c;
    }

    Integer Integer::pow(Integer b)
    {
        Integer c;

        mpz_set(c.modulus, modulus);
  
        if (mpz_cmp_ui(modulus, 0)) {
            mpz_powm(c.value, value, b.value, c.modulus);
        } else {
            mpz_pow_ui(c.value, value, mpz_get_ui(b.value));
        }

        return c;
    }

    std::ostream& operator<<(std::ostream& o, const Integer& a)
    {
        return (o << a.str());
    }

    bool operator==(const Integer& a, const Integer& b)
    {
        return (mpz_cmp(a.value, b.value) == 0);
    }

    bool operator!=(const Integer& a, const Integer& b)
    {
        return (mpz_cmp(a.value, b.value) != 0);
    }

    bool operator>=(const Integer& a, const Integer& b)
    {
        return (mpz_cmp(a.value, b.value) >= 0);
    }

    bool operator>(const Integer& a, const Integer& b)
    {
        return mpz_cmp(a.value, b.value) > 0;
    }

    bool operator<=(const Integer& a, const Integer& b)
    {
        return mpz_cmp(a.value, b.value) <= 0;
    }

    bool operator<(const Integer& a, const Integer& b)
    {
        return mpz_cmp(a.value, b.value) < 0;
    }
}
