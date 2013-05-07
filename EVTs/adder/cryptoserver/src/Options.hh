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
 * @file Options.hh
 * Interface of the Options class.
 */

#ifndef OPTIONS_HH
#define OPTIONS_HH

#include <string>

#include "ace/Null_Mutex.h"
#include "ace/Singleton.h"

#define LOG_LEVEL LM_SHUTDOWN | LM_TRACE | LM_DEBUG | LM_INFO | LM_NOTICE \
        | LM_WARNING | LM_STARTUP | LM_ERROR | LM_CRITICAL | LM_ALERT \
        | LM_EMERGENCY

/**
 * Class to represent the config file options that have been parsed.
 */
class Options
{
public:
    Options();
    ~Options();

    bool load(std::string filename);
    bool parse(int argc, char** argv, std::string &conffile);
    bool read_config_files();

    int port; /**< The local server port. */
    bool daemon; /**< Whether to run the server as a daemon. */
    std::string db_hostname; /**< The database hostname. */
    int db_port; /**< The database port. */
    std::string db_username; /**< The database username. */
    std::string db_password; /**< The database password. */
    std::string db_database; /**< The database name. */
    std::string logging; /**< Logging. */
    int session_time_limit; /**< The time before session
                               expiration. */
    bool admin; /**< Whether to enable the administrator functionality. */
    std::string admin_password; /**< The administrator password. */
};

typedef ACE_Singleton<Options, ACE_Null_Mutex> OptionsSingleton;
#define OPTIONS OptionsSingleton::instance()

#endif /* OPTIONS_HH */
