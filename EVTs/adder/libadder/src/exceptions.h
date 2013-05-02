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
 * @file exceptions.h
 * Defines all of the exceptions.
 */

#ifndef EXCEPTIONS_H
#define EXCEPTIONS_H

#include <string>

#include "common.h"
#include "Vote.h"
#include "Context.h"

namespace adder
{
    class LIBADDER_API Invalid_encoding
    {
    private:
		const char *p;
	public:
        Invalid_encoding(std::string q) { p = q.c_str(); }
        std::string msg() { return std::string(p); }
    };

    class LIBADDER_API Invalid_armor
    {
    private:
		const char *p;
    public:
        Invalid_armor(std::string q) { p = q.c_str(); }
        std::string msg() { return std::string(p); }
    };

    class LIBADDER_API Invalid_key
    {
    private:
		const char *p;
    public:
        Invalid_key(std::string q) { p = q.c_str(); }
        std::string msg() { return std::string(p); }
    };

    class LIBADDER_API Decryption_error
    {
    private:
		const char *p;
    public:
        Decryption_error(std::string q) { p = q.c_str(); }
        std::string msg() { return std::string(p); }
    };

    class LIBADDER_API Armor_error
    {
    private:
		const char *p;
    public:
        Armor_error(std::string q) { p = q.c_str(); }
        std::string msg() { return std::string(p); }
    };

    class LIBADDER_API Invalid_vote
    {
    private:
		const char *p;
    public:
        Invalid_vote(std::string q) { p = q.c_str(); }
        std::string msg() { return std::string(p); }
    };

    class LIBADDER_API Invalid_ciphertext
    {
    private:
		const char *p;
    public:
        Invalid_ciphertext(std::string q) { p = q.c_str(); }
        std::string msg() { return std::string(p); }
    };

    class LIBADDER_API Invalid_sum
    {
    private:
		const char *p;
    public:
        Invalid_sum(std::string q) { p = q.c_str(); }
        std::string msg() { return std::string(p); }
    };

    class LIBADDER_API Invalid_polynomial
    {
    private:
		const char *p;
    public:
        Invalid_polynomial(std::string q) { p = q.c_str(); }
        std::string msg() { return std::string(p); }
    };

    class LIBADDER_API Invalid_proof
    {
    private:
		const char *p;
    public:
        Invalid_proof(std::string q) { p = q.c_str(); }
        std::string msg() { return std::string(p); }
    };
}
#endif /* EXCEPTIONS_H */
