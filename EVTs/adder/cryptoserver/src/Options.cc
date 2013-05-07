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

#include <fstream>
#include <iostream>
#include <vector>
#include <string>
#include <cstdio>

#include "Options.hh"
#include "Utilities.hh"

#undef VERSION
#undef PACKAGE
#undef PACKAGE_BUGREPORT
#undef PACKAGE_NAME
#undef PACKAGE_STRING
#undef PACKAGE_TARNAME
#undef PACKAGE_VERSION
#include "config.h"

/**
 * Constructor. Initializes default values.
 */
Options::Options()
{
    port = 6999;
    daemon = true;
    db_hostname = "localhost";
    db_port = 0; /* Use the default MySQL port by default. */
    db_username = "";
    db_password = "";
    db_database = "";
    admin = true;
    admin_password = "";
    logging = "syslog";
}

/**
 * Destructor.
 */
Options::~Options()
{}

/**
 * Loads the configuration options from the file.
 * @param filename the filename of the config file.
 * @return @b true if the load was successful, @b false otherwise.
 */
bool Options::load(std::string filename)
{
    std::ifstream INFILE((const char*)filename.c_str());
    std::string line;
    std::vector<std::string> tokens;
    bool error = false;
    std::string key;
    std::string value;

    if (!INFILE) {
        return false;
    }

    while (!INFILE.eof()) {
        std::getline(INFILE, line);

        tokens = tokenize(line);

        if (tokens.size() == 0) {
            return false;
        }

        if (tokens[0][0] == '#') {
            //ACE_DEBUG((LM_DEBUG, "comment: %s\n", tokens[0].c_str()));
            continue;
        } else if (tokens[0].empty()) {
            continue;
        } else if (tokens.size() != 2) {
            return false;
        } else {
            key = tokens[0];
            value = tokens[1];
            //ACE_DEBUG((LM_DEBUG, "key=[%s], value=[%s]\n", key.c_str(), value.c_str()));
        }

        if (key == "logging") {
            if (value == "syslog") {
                logging = "syslog";
	    } else if (value == "on") {
                logging = "on";
            } else if (value == "off") {
                logging = "off";
            }

            //ACE_DEBUG((LM_DEBUG, "logging: %s\n", value.c_str()));
        } else if (key == "port") {
            port = ACE_OS::atoi(value.c_str());
            //ACE_DEBUG((LM_DEBUG, "port: %d\n", port));
        } else if (key == "daemon") {
            if (value == "false") {
                daemon = false;
            } else if (value == "true") {
                daemon = true;
            } else {
                error = true;
            }
        } else if (key == "db_hostname") {
            db_hostname = value;
            //ACE_DEBUG((LM_DEBUG, "db_hostname: %s\n", db_hostname.c_str()));
        } else if (key == "db_port") {
            db_port = ACE_OS::atoi(value.c_str());
            //ACE_DEBUG((LM_DEBUG, "db_hostname: %d\n", db_port));
        } else if (key == "db_username") {
            db_username = value;
            //ACE_DEBUG((LM_DEBUG, "db_username: %s\n", db_username.c_str()));
        } else if (key == "db_password") {
            db_password = value;
            //ACE_DEBUG((LM_DEBUG, "db_password: %s\n", db_password.c_str()));
        } else if (key == "db_database") {
            db_database = value;
            //ACE_DEBUG((LM_DEBUG, "db_database: %s\n", db_database.c_str()));
        } else if (key == "session_time_limit") {
            session_time_limit = ACE_OS::atoi(value.c_str());
            //ACE_DEBUG((LM_DEBUG, "session_time_limit: %d\n",
            //session_time_limit));
        } else if (key == "admin") {
            if (value == "false") {
                admin = false;
            } else if (value == "true") {
                admin = true;
            } else {
                error = true;
            }
        } else if (key == "admin_password") {
            admin_password = value;
        } else {
            //ACE_DEBUG((LM_ERROR, "bad_command_option: %s\n", key.c_str()));
            return false;
        }
    }

    return true;
}

/**
 * Gets the command line argument if there is one.
 * @param argc the argument count.
 * @param argv the arguments.
 * @param conffile the variable to hold the path to the configuration file.
 * @return @b true if a filename was passed as an argument, @b false otherwise.
 */
bool Options::parse(int argc, char** argv, std::string &conffile)
{
    if (argc > 1) {
        conffile = argv[1];
        return true;
    } else {
        return false;
    }
}

/**
 * Read the configuration from the configuration files.
 * @return @b true if any single configuration file was loaded, @b false otherwise.
 */
bool Options::read_config_files()
{
    std::string conffile;
    std::vector<std::string> conffiles;
    bool read_config_file = false;
    const char* home = getenv("HOME");

    /* XXX: This is probably insecure. */
    conffiles.push_back("./cryptoserver.conf");

    if (home) {
        conffiles.push_back(std::string(home) + "/.cryptoserver.conf");
    }

    conffiles.push_back(CONFIG_FILE);

    while (!conffiles.empty()) {
        conffile = conffiles.back();

        conffiles.pop_back();

        if (load(conffile)) {
            read_config_file = true;
            //ACE_DEBUG((LM_NOTICE, "reading of config [%s] file passed\n", conffile.c_str()));
        } else {
            //ACE_DEBUG((LM_NOTICE, "reading of config file [%s] failed\n", conffile.c_str()));
        }
    }

    return read_config_file;
}
