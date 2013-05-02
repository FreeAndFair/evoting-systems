/* -*- Mode: C++; tab-width: 4; indent-tabs-mode: nil; c-basic-offset: 4 -*- */

/*  libadder - Cryptographic library for the Adder project.
    Copyright (C) 2004-2006  The Adder Team <adder@cse.uconn.edu>

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
 * @file MembershipProof.h
 * Interface of the MembershipProof class.
 */

#ifndef MEMBERSHIPPROOF_H
#define MEMBERSHIPPROOF_H

#include <string>
#include <vector>

#include "common.h"
#include "Integer.h"

namespace adder
{
    /**
       \brief Zero-knowledge proof of set membership.
       
       Suppose we have a ciphertext \f$\langle G, H \rangle = \langle
       g^r, h^r f^m \rangle\f$ and we wish to prove that \f$m \in
       \{i_1, \ldots, i_n\}\f$. Furthermore, suppose that \f$m =
       i_x\f$. We can use the following OR-composition proof of
       knowledge.

       <table border=0>
       <tr><th>Prover</th><th></th><th>Verifier</th>
       <tr><td>\f$c_1, \ldots, c_n \stackrel{\texttt{r}}{\leftarrow}
       \mathrm{Z}_q\f$</td><td></td><td></td></tr>

       <tr><td>\f$s_1, \ldots, s_n \stackrel{\texttt{r}}{\leftarrow}
       \mathrm{Z}_q\f$</td><td></td><td></td></tr>

       <tr><td>if \f$i \neq x\f$, then \f$y_i \leftarrow
       g^{s_i}G^{-c_i}\f$ and \f$z_i \leftarrow h^{s_i}(H /
       f^{i_i})^{-c_i}\f$<br> otherwise, \f$y_i = g^t\f$ and \f$z_i
       = h^t\f$</td><td></td><td></td></tr>

       <tr><td></td><td>\f$\stackrel{y_1, \ldots, y_n, z_1, \ldots,
       z_n}{\longrightarrow}\f$</td><td></td></tr>

       <tr><td></td><td></td><td>\f$c \stackrel{\texttt{r}}{\leftarrow}
       \mathrm{Z}_q\f$</td></tr>

       <tr><td></td><td>\f$\stackrel{c}{\longleftarrow}\f$</td><td></td></tr>

       <tr><td>\f$c_x = c - c_1 - \cdots -
       c_n\f$</td><td></td><td></td></tr>

       <tr><td>\f$s_x = t + c_x r\f$</td><td></td><td></td></tr>

       <tr><td></td><td>\f$\stackrel{s_1, \ldots, s_n, c_1, \ldots,
       c_n}{\longrightarrow}\f$</td><td></td></tr>

       <tr><td></td><td></td> 
       <td> 
       \f$g^{s_i} \stackrel{?}{=} y_i G^{c_i}\f$ <br> 
       \f$h^{s_i} \stackrel{?}{=} z_i (H/f^{i_i})^{c_i}, i \in 
       \{i_1, \ldots, i_n\}\f$<br>
       \f$c \stackrel{?}{=} c_1 + \cdots + c_n\f$ </td></tr>

       </table>

       Now, we can make this proof non-interactive by employing the
       Fiat-Shamir heuristic.  Then, the prover will send the tuple
       \f$\langle y_1, z_1, \ldots, y_n, z_n, c, s_1, \ldots, s_n,
       c_1, \ldots, c_n\rangle\f$, where \f$c = \mathcal{H}(g, h, G,
       H, y_1, z_1, \ldots, y_n, z_n)\f$ and \f$\mathcal{H}\f$ is a
       cryptographic hash function. Verification is performed by
       testing that \f$c_1 + \cdots + c_n = \mathcal{H}(g, h, G, H,
       g^{s_1}G^{-c_1}, h^{s_1}(H/f^{i_1})^{-c_1}, \ldots,
       g^{s_n}G^{-c_n}, h^{s_n}(H/f^{i_n})^{-c_n})\f$.
     */
    class LIBADDER_API MembershipProof {
    public:
        /**
           Default constructor.
        */
        MembershipProof();

        /**
           Computes a proof.
           @param ciphertext the ciphertext that the proof is being
           performed on.
           @param pub_key the public key used to encrypt the message.
           @param value the plaintext value of the ciphertext.
           @param domain the domain of possible values of the
           plaintext.

           This function will compute a proof as detailed above by
           forming one proof for each element of the domain. All but
           one of the proofs (the one corresponding to \em value) will
           be fake.
        */
        void compute(ElgamalCiphertext ciphertext,
                     PublicKey pub_key,
                     Integer value,
                     std::vector<Integer> domain);
            
        /**
           Verifies a proof.
           @param ciphertext the ciphertext corresponding to the
           proof.
           @param pub_key the public key used to encrypt the message.
           @param domain the domain of possible values of the
           plaintext.
           @return \b true if the proof is valid, \b false otherwise.
        */
        bool verify(ElgamalCiphertext ciphertext, 
                    PublicKey pub_key,
                    std::vector<Integer> domain);
        
        /**
           Returns a string representation of the proof. The string is
           in the form \f$\texttt{p}  p  
           \texttt{y}  y_1  \cdots 
           \texttt{y}  y_n 

           \texttt{z}  z_1  \cdots 
           \texttt{z}  z_n 
           
           \texttt{s}  s_1  \cdots 
           \texttt{s}  s_n 
           
           \texttt{c}  c_1  \cdots 
           \texttt{c}  c_n \f$, where all numbers are expressed in
           base 10.
           @return the string representation of the proof.
        */
        std::string str() const;

        /**
           Loads the proof from a string.
           @param proof_string the string representation of a proof.
           @exception Invalid_proof the string was not well-formed.
           @see str
         */
        void from_str(std::string proof_string);

    private:
#if _MSC_VER
#pragma warning(push)
#pragma warning(disable: 4251)
#endif // _MSC_VER
        std::vector<Integer> y_vec; /**< The vector of \em y -values. */
        std::vector<Integer> z_vec; /**< The vector of \em z -values. */
        std::vector<Integer> s_vec; /**< The vector of \em s -values. */
        std::vector<Integer> c_vec; /**< The vector of \em c -values. */
#if _MSC_VER
#pragma warning(pop)
#endif // _MSC_VER

        Integer c; /**< The challenge component of the proof. */
        Integer p; /**< The modulus. */
    };
}

#endif /* MEMBERSHIPPROOF_H */
