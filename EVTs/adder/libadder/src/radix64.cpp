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
 * @file radix64.cpp
 * Implementations of the various Radix-64 encoding functions.
 */

#ifdef WIN32
#include "config-win32.h"
#else
#include "config.h"
#endif

#include "common.h"
#include "radix64.h"
#include "exceptions.h"

namespace adder {
    /* Radix-64 encoding table */
    char base_64_enc_table[65] = {
        'A','B','C','D','E','F','G','H','I','J','K','L','M','N','O','P','Q','R',
        'S','T','U','V','W','X','Y','Z','a','b','c','d','e','f','g','h','i','j',
        'k','l','m','n','o','p','q','r','s','t','u','v','w','x','y','z','0','1',
        '2','3','4','5','6','7','8','9','+','/'
    };

    /* Radix-64 decoding table */
    unsigned char base_64_dec_table[257] = {
        255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,
        255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,62,255,255,255,63,
        52,53,54,55,56,57,58,59,60,61,255,255,255,255,255,255,255, 0, 1, 2, 3, 4, 5, 6,
         7, 8, 9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,255,255,255,255,255,
        255,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,
        49,50,51,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,
        255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,
        255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,
        255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,
        255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,
        255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255
    };

    LIBADDER_API std::string encode_radix_64(std::string msg)
    {
        std::string enc_msg;
        std::string checksum;

        size_t msg_length = msg.length();
        
        size_t i = 0;
        int count = 0;

        checksum = calc_checksum_CRC24(msg);

        /* Encode 3 bytes input into 4 bytes output */
        while (i <= (msg_length - 3)) {
            enc_msg += base_64_enc_table[(msg[i] >> 2) & 0x3f];
            enc_msg += base_64_enc_table[((msg[i] & 0x3) << 4) |
                                             ((msg[i+1] >> 4) & 0xf)];
            enc_msg += base_64_enc_table[((msg[i+1] & 0xf) << 2) |
                                             ((msg[i+2] >> 6) & 0x3)];
            enc_msg += base_64_enc_table[msg[i+2] & 0x3f];
            i += 3;
            count += 4;
            
            /* Only 64 characters per line */
            if (count == 64) {
                enc_msg += '\n';
                count = 0;
            }
        }
        
        /* If 2 bytes left do */
        if (i == msg_length - 2) {
            enc_msg += base_64_enc_table[(msg[i] >> 2) & 0x3f];
            enc_msg += base_64_enc_table[((msg[i] & 0x3) << 4) |
                                             ((msg[i+1] >> 4) & 0xf)];
            enc_msg += base_64_enc_table[((msg[i+1] & 0xf) << 2)];
            enc_msg += '=';  
        }
        
        /* If 1 byte left do */
        else if (i == msg_length - 1) {
            enc_msg += base_64_enc_table[(msg[i] >> 2) & 0x3f];
            enc_msg += base_64_enc_table[((msg[i] & 0x3) << 4)];
            enc_msg += "==";
        }
           
        enc_msg += '\n';
        enc_msg += checksum;
        enc_msg += '\n';
        
        return enc_msg;
    }

    LIBADDER_API std::string decode_radix_64(std::string enc_msg)
    {
        std::string msg;
        std::string checksum;
        
        size_t i = 0;
        int count = 0;

        size_t msg_length = enc_msg.length();

        /* Strip off checksum */
        checksum += enc_msg[msg_length-6];
        checksum += enc_msg[msg_length-5];
        checksum += enc_msg[msg_length-4];
        checksum += enc_msg[msg_length-3];
        checksum += enc_msg[msg_length-2];

        /* Decode 4 bytes input into 3 bytes output */
        while (i < (msg_length - 8)) {
            /* Check for valid input */
            if (enc_msg[i] < 0 || enc_msg[i+1] < 0 || 
                enc_msg[i+2] < 0 || enc_msg[i+3] < 0) {
                throw Invalid_encoding("invalid encoding");
            }
            msg += ((base_64_dec_table[(int)enc_msg[i]] << 2) | 
                    ((base_64_dec_table[(int)enc_msg[i+1]] >> 4) & 0x3)); 
            if (enc_msg[i+2] != '=') { 
                msg += (((base_64_dec_table[(int)enc_msg[i+1]] & 0xf) << 4) | 
                    ((base_64_dec_table[(int)enc_msg[i+2]] >> 2) & 0xf));
            }
            if (enc_msg[i+3] != '=') {
                msg += (((base_64_dec_table[(int)enc_msg[i+2]] & 0x3) << 6) | 
                    base_64_dec_table[(int)enc_msg[i+3]]);
            }
                            
            i += 4;
            count += 4;
         
            /* Remove \n after 64 characters */
            if (count == 64) {
                if (enc_msg[i] != '\n') {
                    throw Invalid_encoding("invalid encoding");
                }
                i++;
                count = 0;
            }  
        }

        /* Verify checksum */
        if (checksum != calc_checksum_CRC24(msg)) {
            throw Invalid_encoding("invalid checksum");
        }
                               
        return msg;
    }

    LIBADDER_API std::string calc_checksum_CRC24(std::string message)
    {
        size_t msg_length = message.length();
        
        const char *msg = message.c_str();

        long crc = 0xb704cel;
        int i;
    
        std::string checksum;

        while (msg_length--) {
            crc ^= (*msg++) << 16;
            for (i = 0; i < 8; i++) {
                crc <<= 1;
                if (crc & 0x1000000)
                    crc ^= 0x1864cfbL;
            }
        }
        
        crc = crc & 0xffffffL;
        
        checksum += '=';
        checksum += base_64_enc_table[(crc >> 18) & 0x3f];
        checksum += base_64_enc_table[(crc >> 12) & 0x3f];
        checksum += base_64_enc_table[(crc >> 6) & 0x3f];
        checksum += base_64_enc_table[crc & 0x3f];
        
        return checksum;
    }

    LIBADDER_API std::string en_armor(std::string encoded_msg, std::string msg_type)
    {
        std::string armored_msg;
        
        armored_msg += "-----BEGIN ADDER ";
        armored_msg += msg_type;
        armored_msg += "-----\n";
        armored_msg += "Version: Adder " PACKAGE_VERSION "\n\n";
        armored_msg += encoded_msg;
        armored_msg += "-----END ADDER ";
         armored_msg += msg_type;
        armored_msg += "-----\n";      

        return armored_msg;
    }

    LIBADDER_API std::string de_armor(std::string armored_msg, std::string msg_type)
    {
        std::string check_it;
        std::string encoded_msg;
        
        size_t sub_beg;
        size_t sub_length;
        size_t arm_length = armored_msg.length();
        size_t beg_length;
        size_t end_length;

        check_it = "-----BEGIN ADDER ";
        check_it += msg_type;
        check_it += "-----\n";
        check_it += "Version: Adder " PACKAGE_VERSION "\n\n";
        
        beg_length = check_it.length();
        sub_beg = beg_length;

        for (size_t i = 0; i < beg_length; i++) {
            if (armored_msg[i] != check_it[i]) {
                throw Invalid_armor("invalid armor");
            }
        }
        
        check_it = "";
        check_it += "-----END ADDER ";
        check_it += msg_type;
        check_it += "-----\n";
        
        end_length = check_it.length();
        sub_length = arm_length - beg_length - end_length;
        end_length--;
        arm_length--;
        
        for (size_t j = 0; j < end_length; j++) {
            if (armored_msg[arm_length-j] != check_it[end_length-j]) {
                throw Invalid_armor("invalid armor");
            }
        }

        encoded_msg = armored_msg.substr(sub_beg, sub_length);

        return encoded_msg;
    }
}
