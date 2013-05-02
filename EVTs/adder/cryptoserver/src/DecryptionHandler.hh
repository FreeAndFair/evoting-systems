/*  CryptoServer - secure online voting server

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
 * @file DecryptionHandler.hh
 * Implementation and interface of the DecryptionHandler class.
 */

#ifndef DECRYPTIONHANDLER_HH
#define DECRYPTIONHANDLER_HH

#include <string>
#include <vector>
#include <sstream>

#include "ace/Svc_Handler.h"

#include "libadder.h"

#include "ClientHandler.hh"
#include "Options.hh"
#include "Database.hh"

/**
 * Class to manage the decryption.
 */
class DecryptionHandler : public ACE_Task_Base
{
public:
    DecryptionHandler(std::vector< std::vector<adder::Integer> > ps, 
                      std::vector<adder::Integer> c,
                      adder::Vote s, 
                      adder::Integer nv,
                      adder::PublicKey mk, 
                      std::string p, 
                      adder::Context* ctx)
        : master_key(ctx)
    {
        partial_sums = ps;
        coeffs = c;
        sum = s;
        num_votes = nv;
        master_key = mk;
        procedure = p;
    }

    virtual int svc(void)
    {
        Database database;
        adder::Context adder_ctx(true);

        if (!database.open(OPTIONS->db_database, OPTIONS->db_hostname,
                           OPTIONS->db_username, OPTIONS->db_password,
                           OPTIONS->db_port)) {
            return -1;
        }

        database.set_context(&adder_ctx);
        database.set_procedure(procedure);

        std::vector<adder::Integer> results =
            adder::get_final_sum(partial_sums, 
                                 coeffs, 
                                 sum, 
                                 num_votes,
                                 master_key);

        database.post_results(results);

        return 0;
    }

private:
    std::vector< std::vector<adder::Integer> > partial_sums;
    std::vector<adder::Integer> coeffs;
    adder::Vote sum;
    adder::Integer num_votes;
    adder::PublicKey master_key;
    std::string procedure;
};

#endif /* DECRYPTIONHANDLER_HH */
