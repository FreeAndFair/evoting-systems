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
 * @file ElectionTimeoutHandler.hh
 * Implementation and interface of the ElectionTimeoutHandler class.
 */

#ifndef ELECTIONTIMEOUTHANDLER_HH
#define ELECTIONTIMEOUTHANDLER_HH

#include <string>
#include <vector>
#include <sstream>

#include "ace/Svc_Handler.h"
#include "ace/Time_Value.h"

#include "libadder.h"

#include "ClientHandler.hh"
#include "Options.hh"
#include "Database.hh"

/**
 * Class to manage the election timer.
 */
class ElectionTimerHandler : public ACE_Event_Handler
{
public:
    ElectionTimerHandler(std::string proc)
    {
        procedure = proc;
    }

    int handle_timeout(const ACE_Time_Value &current_time, const void* = 0)
    {
        ACE_UNUSED_ARG(current_time);

        ACE_DEBUG((LM_DEBUG, "(%M|%t) election is ending.\n"));

        Database database;
        adder::Context adder_ctx(true);

        if (!database.open(OPTIONS->db_database, OPTIONS->db_hostname,
                           OPTIONS->db_username, OPTIONS->db_password,
                           OPTIONS->db_port)) {
            return -1;
        }

        database.set_context(&adder_ctx);
        database.set_procedure(procedure);

        database.expire_election_timer(procedure);

        ACE_DEBUG((LM_DEBUG, "(%M|%t) election is over.\n"));

        return 0;
    }

private:
    std::string procedure; /**< The procedure ID. */
};

/**
 * Class to manage the secret key timer.
 */
class SecretKeyTimerHandler : public ACE_Event_Handler
{
public:
    SecretKeyTimerHandler(std::string proc)
    {
        procedure = proc;
    }

    int handle_timeout(const ACE_Time_Value &current_time, const void* = 0)
    {
        ACE_UNUSED_ARG(current_time);

        ACE_DEBUG((LM_DEBUG, "(%M|%t) secret key collection is ending.\n"));

        Database database;
        adder::Context adder_ctx(true);

        if (!database.open(OPTIONS->db_database, OPTIONS->db_hostname,
                           OPTIONS->db_username, OPTIONS->db_password,
                           OPTIONS->db_port)) {
            return -1;
        }

        database.set_context(&adder_ctx);
        database.set_procedure(procedure);

        database.expire_secret_key_timer(procedure);

        return 0;
    }

private:
    std::string procedure; /**< The procedure ID. */
};

/**
 * Class to manage the polynomial timer.
 */
class PolynomialTimerHandler : public ACE_Event_Handler
{
public:
    PolynomialTimerHandler(std::string proc)
    {
        procedure = proc;
    }

    int handle_timeout(const ACE_Time_Value &current_time, const void* = 0)
    {
        ACE_UNUSED_ARG(current_time);

        ACE_DEBUG((LM_DEBUG, "(%M|%t) polynomial collection is ending.\n"));

        Database database;
        adder::Context adder_ctx(true);

        if (!database.open(OPTIONS->db_database, OPTIONS->db_hostname,
                           OPTIONS->db_username, OPTIONS->db_password,
                           OPTIONS->db_port)) {
            return -1;
        }

        database.set_context(&adder_ctx);
        database.set_procedure(procedure);

        database.expire_polynomial_timer(procedure);

        return 0;
    }

private:
    std::string procedure; /**< The procedure ID. */
};

/**
 * Class to manage the public key timer.
 */
class PublicKeyTimerHandler : public ACE_Event_Handler
{
public:
    PublicKeyTimerHandler(std::string proc)
    {
        procedure = proc;
    }

    int handle_timeout(const ACE_Time_Value &current_time, const void* = 0)
    {
        ACE_UNUSED_ARG(current_time);

        ACE_DEBUG((LM_DEBUG, "(%M|%t) public key collection is ending.\n"));

        Database database;
        adder::Context adder_ctx(true);

        if (!database.open(OPTIONS->db_database, OPTIONS->db_hostname,
                           OPTIONS->db_username, OPTIONS->db_password,
                           OPTIONS->db_port)) {
            return -1;
        }

        database.set_context(&adder_ctx);
        database.set_procedure(procedure);

        database.expire_public_key_timer(procedure);

        return 0;
    }

private:
    std::string procedure; /**< The procedure ID. */
};

#endif /* ELECTIONTIMEOUTHANDLER_HH */
