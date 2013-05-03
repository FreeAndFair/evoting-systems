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
 * @file misc.h
 * Declares various miscellaneous functions.
 */

#ifndef MISC_H
#define MISC_H

#include <vector>

#include "common.h"
#include "Vote.h"
#include "Context.h"
#include "Integer.h"
#include "PublicKey.h"

namespace adder
{
    LIBADDER_API Vote sum_votes(std::vector<Vote> votes, Integer p);

    LIBADDER_API std::vector<std::string> tokenize(std::string str);

    LIBADDER_API Integer gen_base(Integer num_voters, Integer p, Integer choices);
    LIBADDER_API std::vector<Integer> get_positions(Integer n, Integer num_positions, 
                                                    Integer base, Integer q);
    LIBADDER_API std::string sha1(std::string input);

    LIBADDER_API std::vector<Integer> 
    get_final_sum(std::vector< std::vector<Integer> > partial_sums,
                  std::vector<Integer> coeffs,
                  Vote sum,
                  Integer num_votes,
                  PublicKey master_key);

}

#endif /* MISC_H */
