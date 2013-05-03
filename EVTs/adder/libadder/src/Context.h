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
 * @file Context.h
 * Interface of the Context class.
 */

#ifndef CONTEXT_H
#define CONTEXT_H

#include "common.h"

namespace adder
{
    /**
     * Class to represent a randomness context. It stores a random
     * number generator seed.
     */
    class LIBADDER_API Context {
    public:
        Context();
        Context(bool secure);
        ~Context();

        gmp_randstate_t* get_state();

        void init_state();
        void set_seed_insecure();
        void set_seed(bool secure);

    private:
        unsigned int seed;
        gmp_randstate_t state;
    };
}

#endif /* CONTEXT_H */
