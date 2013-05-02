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

/* This file uses the public domain SHA-1 implementation by 
   Steve Reid <sreid@sea-to-sky.net>
   James H. Brown <jbrown@burgoyne.com>
*/

/**
 * @file misc.cpp
 * Implementations of various miscellaneous functions.
 */

//#define SHA1HANDSOFF 1

#include <ctime>
#include <fstream>
#include <iostream>
#include <sstream>
#include <vector>

#include <stdio.h>
#include <string.h>

#include "common.h"
#include "Context.h"
#include "Vote.h"
#include "PublicKey.h"
#include "Polynomial.h"

#include <openssl/sha.h>

namespace adder {

// #ifndef  i386   /* For ALPHA  (SAK) */
// #ifndef LITTLE_ENDIAN
// #define LITTLE_ENDIAN
// #endif 
//     typedef          long int int64;
//     typedef unsigned long int uint64;
//     typedef          int int32;
//     typedef unsigned int uint32;
// #else  /*i386*/
// #ifndef LITTLE_ENDIAN
// #define LITTLE_ENDIAN
// #endif 
//     typedef          long long int int64;
//     typedef unsigned long long int uint64;
//     typedef          long int int32;
//     typedef unsigned long int uint32;
// #endif /*i386*/


//     /* #include <process.h> */	/* prototype for exit() - JHB */
//     /* Using return() instead of exit() - SWR */

//     typedef struct {
//         uint32 state[5];
//         uint32 count[2];
//         unsigned char buffer[64];
//     } SHA1_CTX;

//     void SHA1Transform(uint32 state[5], const unsigned char buffer[64]);
//     void SHA1Init(SHA1_CTX* context);
//     void SHA1Update(SHA1_CTX* context, const unsigned char* data, uint32 len);	/*
//                                                                               JHB */
//     void SHA1Final(unsigned char digest[20], SHA1_CTX* context);

// #define rol(value, bits) (((value) << (bits)) | ((value) >> (32 - (bits))))

//     /* blk0() and blk() perform the initial expand. */
//     /* I got the idea of expanding during the round function from SSLeay */
// #ifdef LITTLE_ENDIAN
// #define blk0(i) (block->l[i] = (rol(block->l[i],24)&0xFF00FF00) \
//     |(rol(block->l[i],8)&0x00FF00FF))
// #else
// #define blk0(i) block->l[i]
// #endif
// #define blk(i) (block->l[i&15] = rol(block->l[(i+13)&15]^block->l[(i+8)&15] \
//     ^block->l[(i+2)&15]^block->l[i&15],1))

//     /* (R0+R1), R2, R3, R4 are the different operations used in SHA1 */
// #define R0(v,w,x,y,z,i) z+=((w&(x^y))^y)+blk0(i)+0x5A827999+rol(v,5);w=rol(w,30);
// #define R1(v,w,x,y,z,i) z+=((w&(x^y))^y)+blk(i)+0x5A827999+rol(v,5);w=rol(w,30);
// #define R2(v,w,x,y,z,i) z+=(w^x^y)+blk(i)+0x6ED9EBA1+rol(v,5);w=rol(w,30);
// #define R3(v,w,x,y,z,i) z+=(((w|x)&y)|(w&x))+blk(i)+0x8F1BBCDC+rol(v,5);w=rol(w,30);
// #define R4(v,w,x,y,z,i) z+=(w^x^y)+blk(i)+0xCA62C1D6+rol(v,5);w=rol(w,30);


// #ifdef VERBOSE  /* SAK */
//     void SHAPrintContext(SHA1_CTX *context, char *msg){
//         printf("%s (%d,%d) %x %x %x %x %x\n",
//                msg,
//                context->count[0], context->count[1], 
//                context->state[0],
//                context->state[1],
//                context->state[2],
//                context->state[3],
//                context->state[4]);
//     }
// #endif

//     /* Hash a single 512-bit block. This is the core of the algorithm. */

//     void SHA1Transform(uint32 state[5], const unsigned char buffer[64])
//     {
//         uint32 a, b, c, d, e;
//         typedef union {
//             unsigned char c[64];
//             uint32 l[16];
//         } CHAR64LONG16;
//         CHAR64LONG16* block;
// #ifdef SHA1HANDSOFF
//         static unsigned char workspace[64];
//         block = (CHAR64LONG16*)workspace;
//         memcpy(block, buffer, 64);
// #else
//         block = (CHAR64LONG16*)buffer;
// #endif
//         /* Copy context->state[] to working vars */
//         a = state[0];
//         b = state[1];
//         c = state[2];
//         d = state[3];
//         e = state[4];
//         /* 4 rounds of 20 operations each. Loop unrolled. */
//         R0(a,b,c,d,e, 0); R0(e,a,b,c,d, 1); R0(d,e,a,b,c, 2); R0(c,d,e,a,b, 3);
//         R0(b,c,d,e,a, 4); R0(a,b,c,d,e, 5); R0(e,a,b,c,d, 6); R0(d,e,a,b,c, 7);
//         R0(c,d,e,a,b, 8); R0(b,c,d,e,a, 9); R0(a,b,c,d,e,10); R0(e,a,b,c,d,11);
//         R0(d,e,a,b,c,12); R0(c,d,e,a,b,13); R0(b,c,d,e,a,14); R0(a,b,c,d,e,15);
//         R1(e,a,b,c,d,16); R1(d,e,a,b,c,17); R1(c,d,e,a,b,18); R1(b,c,d,e,a,19);
//         R2(a,b,c,d,e,20); R2(e,a,b,c,d,21); R2(d,e,a,b,c,22); R2(c,d,e,a,b,23);
//         R2(b,c,d,e,a,24); R2(a,b,c,d,e,25); R2(e,a,b,c,d,26); R2(d,e,a,b,c,27);
//         R2(c,d,e,a,b,28); R2(b,c,d,e,a,29); R2(a,b,c,d,e,30); R2(e,a,b,c,d,31);
//         R2(d,e,a,b,c,32); R2(c,d,e,a,b,33); R2(b,c,d,e,a,34); R2(a,b,c,d,e,35);
//         R2(e,a,b,c,d,36); R2(d,e,a,b,c,37); R2(c,d,e,a,b,38); R2(b,c,d,e,a,39);
//         R3(a,b,c,d,e,40); R3(e,a,b,c,d,41); R3(d,e,a,b,c,42); R3(c,d,e,a,b,43);
//         R3(b,c,d,e,a,44); R3(a,b,c,d,e,45); R3(e,a,b,c,d,46); R3(d,e,a,b,c,47);
//         R3(c,d,e,a,b,48); R3(b,c,d,e,a,49); R3(a,b,c,d,e,50); R3(e,a,b,c,d,51);
//         R3(d,e,a,b,c,52); R3(c,d,e,a,b,53); R3(b,c,d,e,a,54); R3(a,b,c,d,e,55);
//         R3(e,a,b,c,d,56); R3(d,e,a,b,c,57); R3(c,d,e,a,b,58); R3(b,c,d,e,a,59);
//         R4(a,b,c,d,e,60); R4(e,a,b,c,d,61); R4(d,e,a,b,c,62); R4(c,d,e,a,b,63);
//         R4(b,c,d,e,a,64); R4(a,b,c,d,e,65); R4(e,a,b,c,d,66); R4(d,e,a,b,c,67);
//         R4(c,d,e,a,b,68); R4(b,c,d,e,a,69); R4(a,b,c,d,e,70); R4(e,a,b,c,d,71);
//         R4(d,e,a,b,c,72); R4(c,d,e,a,b,73); R4(b,c,d,e,a,74); R4(a,b,c,d,e,75);
//         R4(e,a,b,c,d,76); R4(d,e,a,b,c,77); R4(c,d,e,a,b,78); R4(b,c,d,e,a,79);
//         /* Add the working vars back into context.state[] */
//         state[0] += a;
//         state[1] += b;
//         state[2] += c;
//         state[3] += d;
//         state[4] += e;
//         /* Wipe variables */
//         a = b = c = d = e = 0;
//     }


//     /* SHA1Init - Initialize new context */

//     void SHA1Init(SHA1_CTX* context)
//     {
//         /* SHA1 initialization constants */
//         context->state[0] = 0x67452301;
//         context->state[1] = 0xEFCDAB89;
//         context->state[2] = 0x98BADCFE;
//         context->state[3] = 0x10325476;
//         context->state[4] = 0xC3D2E1F0;
//         context->count[0] = context->count[1] = 0;
//     }


//     /* Run your data through this. */

//     void SHA1Update(SHA1_CTX* context, const unsigned char* data, uint32 len)	/*
//                                                                           JHB */
//     {
//         uint32 i, j;	/* JHB */

// #ifdef VERBOSE
//         SHAPrintContext(context, "before");
// #endif
//         j = (context->count[0] >> 3) & 63;
//         if ((context->count[0] += len << 3) < (len << 3)) context->count[1]++;
//         context->count[1] += (len >> 29);
//         if ((j + len) > 63) {
//             memcpy(&context->buffer[j], data, (i = 64-j));
//             SHA1Transform(context->state, context->buffer);
//             for ( ; i + 63 < len; i += 64) {
//                 SHA1Transform(context->state, &data[i]);
//             }
//             j = 0;
//         }
//         else i = 0;
//         memcpy(&context->buffer[j], &data[i], len - i);
// #ifdef VERBOSE
//         SHAPrintContext(context, "after ");
// #endif
//     }


//     /* Add padding and return the message digest. */

//     void SHA1Final(unsigned char digest[20], SHA1_CTX* context)
//     {
//         uint32 i;	/* JHB */
//         unsigned char finalcount[8];

//         for (i = 0; i < 8; i++) {
//             finalcount[i] = (unsigned char)((context->count[(i >= 4 ? 0 : 1)]
//                                              >> ((3-(i & 3)) * 8) ) & 255);  /* Endian independent */
//         }
//         SHA1Update(context, (const unsigned char *)"\200", 1);
//         while ((context->count[0] & 504) != 448) {
//             SHA1Update(context, (const unsigned char *)"\0", 1);
//         }
//         SHA1Update(context, finalcount, 8);  /* Should cause a SHA1Transform()
//                                               */
//         for (i = 0; i < 20; i++) {
//             digest[i] = (unsigned char)
//                 ((context->state[i>>2] >> ((3-(i & 3)) * 8) ) & 255);
//         }
//         /* Wipe variables */
//         i = 0;	/* JHB */
//         memset(context->buffer, 0, 64);
//         memset(context->state, 0, 20);
//         memset(context->count, 0, 8);
//         memset(finalcount, 0, 8);	/* SWR */
// #ifdef SHA1HANDSOFF  /* make SHA1Transform overwrite it's own static vars */
//         SHA1Transform(context->state, context->buffer);
// #endif
//     }

//     LIBADDER_API Vote sum_votes(std::vector<Vote> votes, Integer p)
//     {
//         Integer G_total("1", p);
//         Integer H_total("1", p);

//         std::vector<Vote>::iterator iter;

//         for (iter = votes.begin(); iter != votes.end(); iter++) {
//             G_total = G_total * iter->get_G();
//             H_total = H_total * iter->get_H();
//         }

//         Vote sum(G_total, H_total, p);

//         return sum;
//     }

    LIBADDER_API Vote sum_votes(std::vector<Vote> votes, Integer p)
    {
        std::vector<ElgamalCiphertext> init_vec;

        for (size_t i = 0; i < votes[0].get_cipher_vec().size(); i++) {
            init_vec.push_back(ElgamalCiphertext(1, 1, p));
        }

        Vote total(init_vec);
     
        for(unsigned int i = 0; i < votes.size(); i++) {
            total = votes[i] * total;
        }

        return total;
    }

    /**
     * Breaks up a string into a vector of tokens.
     * @param str the string to be tokenized.
     * @return the tokenized string.
     */
    LIBADDER_API std::vector<std::string> tokenize(std::string str)
    {
        std::vector<std::string> t_vect; /* Vector to hold the tokens */
        std::vector<std::string>::iterator v_iter;
        std::string temp_str = "";

        for (unsigned int i = 0; i < str.length(); i++) {
            while (!isspace(str[i]) && i < str.length()) {
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
    
    LIBADDER_API Integer gen_base(Integer num_voters, Integer p, Integer choices)
    {
        Integer q = (p - 1) / 2;
        Integer M = Integer(num_voters, p);
        
        while (M.pow(choices) >= q) {
            M = M + 1;
        }
        
        return M;
    }
    
    LIBADDER_API std::vector<Integer> get_positions(Integer n, Integer num_positions, 
                                                    Integer base, Integer q)
    {
        std::vector<Integer> result;

        // These will have whatever modulus base has
        Integer goal = 0;
        Integer subtract = 0;

        for (int i = 0; i < num_positions; i++) {
            goal = base.pow(Integer(i + 1));
            subtract = base.pow(Integer(i));

            int count = 0;

            while (!n.divisible(goal)) {
                n = n - subtract;
                count++;
            }

            result.push_back(Integer(count));
        }

        return result;
    }

    LIBADDER_API std::vector<Integer> 
    get_final_sum(std::vector< std::vector<Integer> > partial_sums,
                  std::vector<Integer> coeffs,
                  Vote sum,
                  Integer num_votes,
                  PublicKey master_key)
    {
        Integer p = master_key.get_p();
        Integer f = master_key.get_f();
        Integer g = master_key.get_g();

        std::vector<adder::Integer> lagrange_coeffs;
        lagrange_coeffs = Polynomial::lagrange(coeffs, p);

        std::vector<Integer> product_vec;

        std::vector<Integer> results;

        std::vector<ElgamalCiphertext> cipher_vec = sum.get_cipher_vec();
        for (unsigned int i = 0; i < cipher_vec.size(); i++) {
            product_vec.push_back(adder::Integer("1", p, 10));

            for (unsigned int j = 0; j < lagrange_coeffs.size(); j++) {
                product_vec[i] = 
                    product_vec[i] * 
                    partial_sums[j][i].pow(lagrange_coeffs[j]);
            }

            Integer H = cipher_vec[i].get_H();
            Integer target = H / product_vec[i];
            Integer j;

            for (j = Integer("0", 10); j <= num_votes; j = j + 1) {
                if (f.pow(j) == target) {
                    break;
                }
            }

            results.push_back(j);
        }

        return results;
    }
                                                  
    LIBADDER_API std::string sha1(std::string input)
    {
        unsigned char digest[20];
        SHA1((const unsigned char*)input.c_str(), input.length(), digest);
        
        char hexchars[16] = {'0', '1', '2', '3', '4', '5', '6', '7', 
                             '8', '9', 'a', 'b', 'c', 'd', 'e', 'f'};
        
        std::stringstream output;
        
        for (int i = 0; i < 20; i++) {
            output << hexchars[(digest[i] >> 4) & 0x0f];
            output << hexchars[digest[i] & 0x0f];
        }
        
        return output.str();
    }
}
