/*  CryptoServer - secure online voting server
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
 * @file Utilities.cc
 * Implementations of utility functions.
 */

#include <iostream>

#include "Utilities.hh"

/**
 * Breaks up a string into a vector of tokens.
 * @param string the string to be tokenized.
 * @return the tokenized string.
 */
std::vector<std::string> tokenize(std::string str)
{
    std::vector<std::string> t_vect; // Vector to hold the tokens
    std::string temp_str = "";

    for (unsigned int i = 0; i < str.length(); i++) {
	while (!isspace(str[i]) and i < str.length()) {
	    temp_str.append(1, str[i]);
	    i++;
	}
	if (temp_str.length() > 0) {
	    t_vect.push_back(temp_str);
	    temp_str = "";
	}
    }

    if (t_vect.size() == 0) {
        t_vect.push_back("");
    }

    return t_vect;
}

std::vector<std::string> tokenize(std::string str, char delim)
{
    std::vector<std::string> t_vect; // Vector to hold the tokens
    std::string temp_str = "";

    for (unsigned int i = 0; i < str.length(); i++) {
	while (str[i] != delim and i < str.length()) {
	    temp_str.append(1, str[i]);
	    i++;
	}
	if (temp_str.length() > 0) {
	    t_vect.push_back(temp_str);
	    temp_str = "";
	}
    }

    if (t_vect.size() == 0) {
        t_vect.push_back("");
    }

    int length = 0;
    std::vector<std::string>::iterator i;

    for (i = t_vect.begin(); i != t_vect.end(); i++) {
        length += (*i).length();
    }

    return t_vect;
}

/**
 * Returns a string representation of a long integer.
 * @param number the long integer to be converted.
 * @return the string representation of @param number.
 */
std::string ltoa(long number) {
    std::string num_str;
    char digit[2];

    digit[1] = '\0';
    digit[0] = char(number % 10 + '0');

    num_str.append(digit);

    while (number > 9) {
        number /= 10;
        digit[0] = char(number % 10 + '0');
        num_str.append(digit);
    }

    if (number < 0) {
        num_str.append("-");
    }

    reverse(num_str.begin(), num_str.end());

    return num_str;
}
