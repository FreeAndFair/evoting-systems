/* -*- Mode: C++; tab-width: 4; indent-tabs-mode: nil; c-basic-offset: 4 -*- */

/*  libadder - Cryptographic library for the Adder project.
    Copyright (C) 2004  The Adder Team

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
 * @file radix64.h
 * Contains declarations of various functions related to Radix-64 encoding.
 */

#ifndef RADIX64_H
#define RADIX64_H

#include <sstream>
#include <vector>

#include "common.h"
#include "PrivateKey.h"
#include "PublicKey.h"
#include "Vote.h"
#include "Context.h"

namespace adder {
    LIBADDER_API std::string encode_radix_64(std::string msg);
    LIBADDER_API std::string decode_radix_64(std::string enc_msg);
    LIBADDER_API std::string calc_checksum_CRC24(std::string message);
    LIBADDER_API std::string en_armor(std::string encoded_msg, std::string msg_type);
    LIBADDER_API std::string de_armor(std::string armored_msg, std::string msg_type);
}

#endif /* RADIX64_H */
