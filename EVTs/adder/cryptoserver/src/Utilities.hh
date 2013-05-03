/*  CryptoServer - secure online voting server
    Copyright (C) 2004  Michael J. Korman <mike@taequin.org>

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
 * @file Utilities.hh
 * Prototypes for the utility functions and other things.
 */

#ifndef UTILITIES_HH
#define UTILITIES_HH

#include <vector>
#include <string>

std::vector<std::string> tokenize(std::string str);
std::vector<std::string> tokenize(std::string str, char delim);
std::string ltoa(long number);


/* This is an exception-based form of assertion.  Use it as follows:
   Assert<exception> (condition);
   to throw 'exception' if 'condition' fails.
   From Stroustrup.
*/
template <class X, class A> inline void Assert(A assertion)
{
    if (!assertion) {
        throw X();
    }
}

#endif /* UTILITIES_HH */
