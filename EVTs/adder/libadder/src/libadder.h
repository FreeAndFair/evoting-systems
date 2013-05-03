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
  \file libadder.h
  Summary header file for Libadder.
*/

/**
  \mainpage Adder Cryptographic Library
  
  \section introduction Introduction

  This is the documentation for the Adder Cryptographic Library
  (libadder).  The library supports threshold homomorphic Elgamal
  encryption with applications to electronic voting.  It is currently
  used by the <a href="http://cryptodrm.engr.uconn.edu/adder/">Adder
  voting system</a>.

  \section features Features
  
  Libadder supports the following features:
  
  - Elgamal public and private keys (adder::PublicKey and
  adder::PrivateKey)
  - Zero-knowledge proofs of set membership (adder::BallotProof)

  \section cryptographic_parameters Cryptographic Parameters
  
  Throughout this documentation, certain symbols are used without
  further explanation.

  - \f$p\f$ is a large prime.
  - \f$q\f$ is a prime divisor of \f$p - 1\f$.
  - \f$g\f$ is the generator of a \f$q\f$-order subgroup of \f$\mathrm{Z}_p\f$.
  
 */

#ifndef LIBADDER_H
#define LIBADDER_H

#include <sstream>
#include <vector>

#include "common.h"
#include "Vote.h"
#include "Context.h"
#include "PublicKey.h"
#include "PrivateKey.h"
#include "radix64.h"
#include "misc.h"
#include "exceptions.h"
#include "Polynomial.h"

#endif /* LIBADDER_H */
