/*  CryptoServer - secure online voting server
    Copyright (C) 2004, 2005, 2006  The Adder Team

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
 * @file Database.cc
 * Interface of the Database class.
 */

#include <stdexcept>
#include <cstdlib>
#include <cstring>
#include <ctime>
#include <vector>
#include <string>

#include "exceptions.h"
#include "misc.h"
#include "Polynomial.h"

#include "Database.hh"
#include "Options.hh"
#include "Utilities.hh"
#include "ElectionTimeoutHandler.hh"
#include "DecryptionHandler.hh"

#include "ace/Acceptor.h"
#include "ace/Signal.h"
#include "ace/OS.h"

#ifdef ENABLE_SSL
#include "ace/SSL/sslconf.h"
#endif

/**
 * Constructor.
 */
Database::Database() : conn(false), query(conn.query()), procedure("\0"), user(""),
                       is_authority(false)
{

}

/**
 * Destructor.
 */
Database::~Database()
{

}

/**
 * Forms a connection to the database
 *
 * @param db the name of the database
 * @param host the hostname of the database server
 * @param user the username of the database user
 * @param password the password of the database server
 * @param port the port of the database server
 * @return true if successful or false otherwise
 */
bool Database::open(std::string db, std::string host,
                    std::string user, std::string password,
                    int port)
{
#if ENABLE_SSL
    ACE_DEBUG((LM_INFO, "SSL enabled for database connection\n"));
    conn.enable_ssl();
#else
    ACE_DEBUG((LM_WARNING, "SSL disabled for database connection\n"));
#endif

    ACE_DEBUG((LM_DEBUG, "Connecting to database (%s, %s, %s)\n",
               db.c_str(), host.c_str(), user.c_str()));

    try {
        /* 
         * FIXME: So what actually happens if the connection fails here?
         * It looks like other requests will just continue to come
         * through and crash the server.
         */ 
        if (user.empty()) {
            conn.connect(db.c_str(), host.c_str(), "", "", port);
        } else {
            conn.connect(db.c_str(), host.c_str(), user.c_str(), password.c_str(), port);
        }
    } catch (const ConnectionFailed& e) {
        ACE_DEBUG((LM_ERROR, "Connecting to database failed: %s\n", e.what()));
    } catch (const Exception& e) {
        ACE_DEBUG((LM_ERROR, "Could not open database connection: %s\n", e.what()));
        return false;
    }

    return true;
}

/**
 * Closes the database connection.
 */
void Database::close()
{
    conn.close();
}

/**
 * Determines if a user_id/password pair is authentic.
 * @param user_id the user_id.
 * @param password the password.
 * @param authority will be set to the value of the is_authority column.
 * @param session_id will be set to the value of the session_id.
 * @return @b true if the pair is authentic, @b false otherwise.
 */
bool Database::authenticate(std::string user_id, std::string password,
                            std::string &authority, std::string &session_id,
                            std::string procedure)
{
    ACE_DEBUG((LM_DEBUG, "Authenticating %s...\n", user_id.c_str()));

    query.reset();
    query << "SELECT password FROM users WHERE user_id = %0q";
    query.parse();

    Result res = query.store(user_id);

    Assert<Errors::Baduser> (res.size() == 1); // Make sure user exists.

    Result::iterator i = res.begin();
    Row row = *i;

    std::string db_password(row["password"]);
    std::string user_password;

    query.reset();
    query << "SELECT salt FROM users WHERE user_id = %0q";
    query.parse();

    res = query.store(user_id);

    i = res.begin();
    row = *i;

    std::string db_salt(row["salt"]);
    ACE_DEBUG((LM_DEBUG, "salt = %s\n", db_salt.c_str()));

    //    user_password = adder::sha1(password + db_salt);
    user_password = password; // FIXME: adder::sha1 is broken
    // FIXME: remove this from the log once it works
    ACE_DEBUG((LM_DEBUG, "real password = %s, db password = %s\n", user_password.c_str(), db_password.c_str()));

    Assert<Errors::Baduser> (user_password == db_password);

    query.reset();
    query << "SELECT * FROM is_authority WHERE user_id = %0q AND proc_id = %1q";
    query.parse();

    res = query.store(user_id, procedure);

    authority = (res.size() == 1 ? "1" : "0");
    is_authority = (res.size() == 1 ? true : false);

    try {
        session_id = create_session_id(user_id);
    } catch (...) {
        ACE_DEBUG((LM_ERROR, "error setting session id\n"));
    }

    if (!is_authority) {
        switch (get_stage(procedure)) {
        case STAGE_WAITKEYS:  // User is not an authority, and stage is auth-only.
        case STAGE_WAITPOLYNOMIAL:
        case STAGE_WAITGETPRIVKEYS:
        case STAGE_WAITDECRYPT:
            throw Errors::Badstage();
            break;
        default:
            set_user(user_id);
            return true;
        }
    } else {
        set_user(user_id);
        return true;
    }
}

/**
 * Determines if session_id is valid (i.e. if the user is logged in).
 * @param session_id the session_id.
 * @param user_id will be set to the value of the user_id.
 * @param authority will be set to the value of the is_authority column.
 * @return @b true if the pair is authentic, @b false otherwise.
 */
bool Database::authenticate(std::string session_id, std::string &user_id,
                            std::string &authority, std::string procedure)
{
    ACE_DEBUG((LM_DEBUG, "Authenticating %s...\n", user_id.c_str()));

    query.reset();
    query << "SELECT user_id, (NOW()+0) - session_start AS delta_t "
          << "FROM users WHERE session_id = %0q";
    query.parse();

    Result res = query.store(session_id);

    Assert<Errors::Baduser> (res.size() == 1);

    Result::iterator i = res.begin();
    Row row = *i;

    Assert<Errors::Badsession> 
        (atol(row["delta_t"]) <= OPTIONS->session_time_limit);

    user_id = std::string(row["user_id"]);
    set_user(user_id);
    
    query.reset();
    query << "SELECT * FROM is_authority WHERE user_id = %0q AND proc_id = %1q";
    query.parse();

    res = query.store(user_id, procedure);

    authority = (res.size() == 1 ? "1" : "0");
    is_authority = (res.size() == 1 ? true : false);

    return true;
}

/**
 * Create a unique session id for a user and store it in the database.
 * @param user_id the user_id.
 * @return the session id.
 */
std::string Database::create_session_id(std::string user_id)
{
    std::string session_id = user_id;

    session_id.append(ltoa(ACE_OS::time(NULL)));
    ACE_OS::srand(ACE_OS::time(NULL));
    session_id.append(ltoa(rand()));
    session_id = adder::sha1(session_id);

    /* 
     * FIXME: Why are we putting the session id in the database?
     * This value should not be public, and should not be needed by the db.
     */
    try {
        query.reset();
        query << "UPDATE users SET session_id= %0q, session_start=(NOW()+0) "
              << "WHERE user_id= %1q";
        query.parse();

        query.execute(session_id, user_id);
    } catch (...) {
        ACE_DEBUG((LM_ERROR, "Error setting session id\n"));
    }

    return session_id;
}

/**
 * End the session by pushing back the session start time.
 * @param session_id the session_id.
 * @return @b true if successful, @b false otherwise.
 */
bool Database::logout(std::string session_id)
{
    try {
        query.reset();
        query << "UPDATE users SET session_start=(NOW()-%0) WHERE session_id=%1q";
        query.parse();

        query.execute(OPTIONS->session_time_limit, session_id);
    } catch (...) {
        ACE_DEBUG((LM_ERROR, "Error setting session id\n"));
        return false;
    }

    return true;
}

/**
 * Determines if a user has already submitted a vote.
 * @param user_id the user_id.
 * @return @b true if the vote slot is full, @b false otherwise.
 */
bool Database::already_voted(std::string procedure)
{
    ACE_DEBUG((LM_DEBUG, "Checking for duplicate vote...\n"));

    query.reset();
    query << "SELECT * FROM choice WHERE user_id = %0q AND proc_id = %1q";
    query.parse();

    Result res = query.store(user, procedure);

    if (res.size() != 1) {
        return false;
    }

    Result::iterator i = res.begin();
    Row row = *i;

    if (row["choice"] == "") {
        ACE_DEBUG((LM_DEBUG, "No vote\n"));
        return false;
    } else {
        ACE_DEBUG((LM_WARNING, "Already voted\n"));
        return true;
    }
}

/**
 * Determines if a user has already submitted a public key.
 * @param user_id the user_id.
 * @return @b true if the key slot is full, @b false otherwise.
 */
bool Database::already_submitted_key(std::string procedure)
{
    ACE_DEBUG((LM_DEBUG, "Checking for duplicate key...\n"));

    query.reset();
    query << "SELECT public_key FROM is_authority "
          << "WHERE user_id = %0q AND proc_id = %1q";
    query.parse();

    Result res = query.store(user, procedure);

    if (res.size() != 1) {
        return false;
    }

    Result::iterator i = res.begin();
    Row row = *i;

    if (std::string((const char*)row["public_key"]) == "") {
        ACE_DEBUG((LM_DEBUG, "No key\n"));
        return false;
    } else {
        ACE_DEBUG((LM_WARNING, "Already submitted key: $%s$\n", (const char*)row["public_key"]));
        return true;
    }
}

/**
 * Determines if an authority has already submitted a partial decryption sum.
 * @return @b true if the authority has already submitted a sum, @b false
 * otherwise.
 */
bool Database::already_submitted_sum(std::string procedure)
{
    ACE_DEBUG((LM_DEBUG, "Checking for duplicate sum...\n"));

    query.reset();
    query << "SELECT partial_decryption_sum FROM preresult "
          << "WHERE user_id = %0q AND proc_id = %1q";
    query.parse();

    Result res = query.store(user, procedure);

    if (res.size() != 1) {
        return false;
    }

    Result::iterator i = res.begin();
    Row row = *i;

    if (row["partial_decryption_sum"] == "") {
        ACE_DEBUG((LM_DEBUG, "No sum\n"));
        return false;
    } else {
        ACE_DEBUG((LM_WARNING, "Already submitted sum\n"));
        return true;
    }
}

/**
 * Determines if a procedure exists.
 * @param proc_id the procedure ID.
 * @return @b true if the procedure exists, @b false otherwise.
 */
bool Database::procedure_exists(std::string proc_id)
{
    query.reset();
    query << "SELECT proc_id FROM proc WHERE proc_id = %0q";
    query.parse();

    Result res = query.store(proc_id);

    if (res.size() == 1) {
        return true;
    } else {
        return false;
    }
}

/**
 * Retrieves the procedure public key.
 * @return the procedure public key.
 */
adder::PublicKey Database::get_pub_key(std::string procedure)
{
    query.reset();
    query << "SELECT public_key FROM proc_pubkey WHERE proc_id = %0q";
    query.parse();

    Result res;

    //    try {
    res = query.store(procedure);
        //    } catch (...) {
        //        return "";
        //    }

    Result::iterator i = res.begin();
    Row row = *i;

    adder::PublicKey pub_key(adder_ctx);

    Assert<Errors::Empty> (res.size() != 0);

    std::string pub_key_str(row["public_key"]);
    
    try {
        pub_key.from_str(pub_key_str);
    } catch (adder::Invalid_key e) {
        ACE_DEBUG((LM_ERROR, "Error getting procedure public key: %s\n", ""));
        return pub_key;
    }

    return pub_key;
}

/**
 * Returns the number of authorities that are currently present.
 * @return the number of authorities.
 */
int Database::get_authority_count(std::string procedure)
{
    STAGE s = get_stage(procedure);

    query.reset();
    query << "SELECT COUNT(*) FROM is_authority WHERE stage = %0 AND proc_id = %1q";
    query.parse();

    Result res;

    if (s < STAGE_COMPUTINGPUBKEY) {
        res = query.store(s, procedure);
    } else if (s == STAGE_WAITDECRYPT) {
        res = query.store(STAGE_WAITDECRYPT, procedure);
    } else {
        res = query.store(STAGE_WAITGETPRIVKEYS, procedure);
    }

    Result::iterator i = res.begin();
    Row row = *i;

    std::ostringstream num_authorities;
    num_authorities << row["COUNT(*)"];

    return ACE_OS::atoi(num_authorities.str().c_str());
}

int Database::get_remaining_authorities(std::string procedure)
{
    int remaining = (get_threshold(procedure) * get_robustness(procedure)) 
        - get_authority_count(procedure);

    if (remaining <= 0) {
        return 0;
    } else {
        return remaining;
    }
}

/**
 * Computes the total sum and stores it.
 */
void Database::compute_sum(std::string procedure)
{
    adder::PublicKey pub_key(adder_ctx);

    try {
        pub_key = get_pub_key(procedure);
    } catch (...) {
        return;
    }

    adder::Integer modulus = pub_key.get_p();

    query.reset();
    query << "SELECT choice FROM choice WHERE proc_id = %0q";
    query.parse();

    Result res = query.store(procedure);
    Result::iterator i;

    std::vector<adder::Vote> votes;
    int num_votes = 0;

    for (i = res.begin(); i != res.end(); i++) {
        Row row = *i;
        std::string vote_str(row["choice"]);
        adder::Vote vote;

        try {
            vote.from_str(vote_str);
        } catch (adder::Invalid_vote e) {
            ACE_DEBUG((LM_ERROR, "Error loading vote: %s\n", ""));
            num_votes = 0;
            return;
        }

        votes.push_back(vote);
        ACE_DEBUG((LM_DEBUG, "Adding vote %s...\n", vote.str().c_str()));
        num_votes++;
    }

    adder::Vote sum = adder::sum_votes(votes, modulus);
    
    try {
        query.reset();
        query << "INSERT INTO cipher_result VALUES(%0q, %1q, %2)";
        query.parse();

        query.execute(procedure, sum.str(), num_votes);
    } catch (...) {
        ACE_DEBUG((LM_ERROR, "Sum has already been computed\n"));
    }
}

/**
 * Aggregates the public keys and stores the result.
 */
void Database::aggregate_keys(std::string procedure)
{
    query.reset();
    query << "SELECT value FROM auth_g_values "
          << "WHERE proc_id = %0q AND number = 0";
    query.parse();

    Result res = query.store(procedure);
    Result::iterator i;

    adder::PublicKey master_key = get_master_key(procedure);
    adder::Integer p = master_key.get_p();

    adder::Integer h("1", p, 10);

    for (i = res.begin(); i != res.end(); i++) {
        Row row = *i;
        h = h * adder::Integer(std::string(row["value"]), p, 10);
    }

    adder::PublicKey server_pub_key(adder_ctx,
                                    p,
                                    master_key.get_g(),
                                    h,
                                    master_key.get_f());

    try {
        query.reset();
        query << "INSERT INTO proc_pubkey VALUES(%0q, %1q)";
        query.parse();

        query.execute(procedure, server_pub_key.str());
    } catch (...) {
        ACE_DEBUG((LM_ERROR,
                 "Public key has already been aggregated for procedure %s\n",
                 procedure.c_str()));
    }
}

/**
 * Decrypts the final sum.
 */
void Database::decrypt_sum(std::string procedure)
{
    adder::PublicKey master_key = get_master_key(procedure);

    adder::Integer p = master_key.get_p();
    adder::Integer f = master_key.get_f();
    adder::Integer g = master_key.get_g();

    adder::Integer q = (p - 1) / 2;

    adder::Polynomial polynomial(adder_ctx,
                                 master_key.get_p(),
                                 master_key.get_g(),
                                 master_key.get_f());

    query.reset();
    query << "SELECT preresult.user_id, is_authority.number,"
          << "preresult.partial_decryption_sum "
          << "FROM is_authority, preresult WHERE "
          << "preresult.user_id = is_authority.user_id AND "
          << "preresult.proc_id = is_authority.proc_id AND "
          << "preresult.proc_id = %0q";
    query.parse();

    Result res = query.store(procedure);

    std::vector<adder::Integer> coeffs;

    Result::iterator i;

    std::vector< std::vector<adder::Integer> > partial_sums;

    for (i = res.begin(); i != res.end(); i++) {
        Row row = *i;
        adder::Integer auth_id(std::string(row["number"]), q, 10);
        std::string partial_decryption(row["partial_decryption_sum"]);

        coeffs.push_back(auth_id);

        std::vector<std::string> sum_vec = tokenize(partial_decryption);

        std::vector<adder::Integer> auth_vec;
        for (unsigned int j = 0; j < sum_vec.size(); j++) {
            auth_vec.push_back(adder::Integer(sum_vec[j], p, 10));
            ACE_DEBUG((LM_DEBUG, "Added to auth_vec: %s\n", auth_vec[j].str().c_str()));
        }

        partial_sums.push_back(auth_vec);
    }

    adder::Vote sum = get_sum(procedure);

    DecryptionHandler* dh = new DecryptionHandler(partial_sums,
                                                  coeffs,
                                                  sum,
                                                  get_num_votes(procedure),
                                                  master_key, 
                                                  procedure, 
                                                  adder_ctx);

    set_stage(procedure, STAGE_DECRYPTING);
    dh->activate(THR_DETACHED);
}

void Database::post_results(std::vector<adder::Integer> results)
{
    int choice_id = 0;
    std::vector<adder::Integer>::iterator j;
    try {
        for (j = results.begin(); j != results.end(); j++, choice_id++) {
            query.reset();
            query << "INSERT INTO result VALUES(%0q, %1, %2q)";
            query.parse();
            query.execute(procedure, choice_id, j->str());
        }
    } catch (...) {
    }

    set_stage(procedure, STAGE_FINISHED);
}

/**
 * Gets the encrypted sum.
 * @return the sum.
 */
adder::Vote Database::get_sum(std::string procedure)
{
    query.reset();
    query << "SELECT cipher_sum FROM cipher_result WHERE proc_id = %0q";
    query.parse();

    Result res = query.store(procedure);

    Result::iterator i = res.begin();
    Row row = *i;

    std::string cipher_sum_str(row["cipher_sum"]);

    adder::Vote cipher_sum;

    try {
        cipher_sum.from_str(cipher_sum_str);
    } catch (adder::Invalid_vote e) {
        ACE_DEBUG((LM_ERROR, "Error getting vote sum: %s\n", ""));
        return cipher_sum;
    }

    return cipher_sum;
}

/**
 * Gets the total number of users who have voted.
 * @return the number of users who have voted.
 */
std::string Database::get_num_votes(std::string procedure)
{
    query.reset();
    query << "SELECT vote_count FROM cipher_result WHERE proc_id = %0q";
    query.parse();

    Result res = query.store(procedure);

    Result::iterator i = res.begin();
    Row row = *i;

    std::ostringstream num_votes;
    num_votes << row["vote_count"];

    return num_votes.str();
}

/**
 * Gets the total number of voters.
 * @return the total number of voters.
 */
int Database::get_num_voters()
{
    query.reset();
    query << "SELECT COUNT(*) FROM users";

    Result res = query.store();

    Result::iterator i = res.begin();
    Row row = *i;

    std::ostringstream num_voters;
    num_voters << row["COUNT(*)"];

    return ACE_OS::atoi(num_voters.str().c_str());
}

/**
 * Gets the total number of choices.
 * @return the total number of choices.
 */
int Database::get_num_choices(std::string proc_id)
{
    query.reset();
    query << "SELECT COUNT(*) FROM proc_choice WHERE proc_id = %0q";
    query.parse();

    Result res = query.store(proc_id);

    Assert<Errors::Critical> (res.size() == 1);

    Result::iterator i = res.begin();
    Row row = *i;

    std::ostringstream num_choices;
    num_choices << row["COUNT(*)"];

    return ACE_OS::atoi(num_choices.str().c_str());
}

/**
 * Gets the minimum number of choices.
 * @return the minimum number choices.
 */
int Database::get_min_choices(std::string procedure)
{
    query.reset();
    query << "SELECT minchoices FROM proc WHERE proc_id = %0q";
    query.parse();

    Result res = query.store(procedure);

    Result::iterator i = res.begin();
    Row row = *i;

    std::ostringstream num_votes;
    num_votes << row["minchoices"];

    return ACE_OS::atoi(num_votes.str().c_str());
}

/**
 * Gets the maximum number of choices.
 * @return the maximum number choices.
 */
int Database::get_max_choices(std::string procedure)
{
    query.reset();
    query << "SELECT maxchoices FROM proc WHERE proc_id = %0q";
    query.parse();

    Result res = query.store(procedure);

    Result::iterator i = res.begin();
    Row row = *i;

    std::ostringstream num_votes;
    num_votes << row["maxchoices"];

    return ACE_OS::atoi(num_votes.str().c_str());
}

/**
 * Get the list of all active procedures.
 * @return a string containing all of the procedures' IDs and titles.
 */
std::string Database::get_procedure_list()
{
    query.reset();
    query << "SELECT proc.proc_id, proc.title, proc_data.stage, proc.threshold, proc.robustness, proc.minchoices, proc.maxchoices  FROM proc, proc_data WHERE "
          << "proc.proc_id = proc_data.proc_id";// AND "
        //          << "proc.start_date <= NOW() AND proc.end_date >= NOW() ";

    Result res;

    //    try {
    res = query.store();
    //    } catch (...) {
    //        return "";
    //    }

    if (res.size() == 0) {
        return "";
    }

    Result::iterator i;
    std::stringstream proc_str;

//     proc_str << "";

//     for (i = res.begin(); i != res.end(); i++) {
//        Row row = *i;
//        proc_str << row["proc_id"]
//                  << row["title"]
//                 << "'" << row["stage"] << "'\n";
//     }

    dont_quote_auto = true;
    for (i = res.begin(); i != res.end(); i++) {
        Row row = *i;
        proc_str << "(\"" << row["proc_id"] << "\","
                 << "\"" << row["title"] << "\","
                 << row["stage"] << ","
                 << get_remaining_authorities(std::string(row["proc_id"])) << ","
                 << row["threshold"] << ","
                 << row["robustness"] << ","
                 << row["minchoices"] << ","
                 << row["maxchoices"]
                 << "),";
    }
    dont_quote_auto = false;

    std::string proc_string(proc_str.str());    
    proc_string.erase(proc_string.length() - 1); // Remove the trailing comma.
        
    return proc_string;
}

/**
 * Get the list of all active procedures.
 * @return a string containing all of the procedures' IDs and titles.
 */
std::string Database::get_procedure_list2()
{
    query.reset();
    query << "SELECT proc.proc_id, proc.title, proc_data.stage FROM proc, proc_data WHERE "
          << "proc.proc_id = proc_data.proc_id";// AND "
        //          << "proc.start_date <= NOW() AND proc.end_date >= NOW() ";

    Result res;

    //    try {
    res = query.store();
    //    } catch (...) {
    //        return "";
    //    }

    if (res.size() == 0) {
        return "";
    }

    Result::iterator i;
    std::stringstream proc_str;

    proc_str << "";

    for (i = res.begin(); i != res.end(); i++) {
       Row row = *i;
       proc_str << row["proc_id"]
                 << row["title"]
                << "'" << row["stage"] << "'\n";
    }

    std::string proc_string(proc_str.str());

    return proc_string;
}

/**
 * Get the list of all users.
 * @return a string containing all of the users' IDs.
 */
std::string Database::get_user_list()
{
    query.reset();
    query << "SELECT user_id FROM users WHERE deleted = 0";

    Result res;

    //    try {
    res = query.store();
    //    } catch (...) {
    //        return 0;
    //    }

    if (res.size() == 0) {
        return "";
    }

    Result::iterator i;
    std::stringstream user_str;

    user_str << "(";

    dont_quote_auto = true;
    for (i = res.begin(); i != res.end(); i++) {
       Row row = *i;
       user_str << "\"" << row["user_id"] << "\",";
    }
    dont_quote_auto = false;

    std::string user_string(user_str.str());
    user_string.erase(user_string.length() - 1);

    return user_string + ")\n";
}

/**
 * Get the list of all users.
 * @return a string containing all of the users' IDs.
 */
std::string Database::get_user_list2()
{
    query.reset();
    query << "SELECT user_id FROM users WHERE deleted = 0";

    Result res;

    //    try {
    res = query.store();
    //    } catch (...) {
    //        return 0;
    //    }

    if (res.size() == 0) {
        return "";
    }

    Result::iterator i;
    std::stringstream user_str;

    for (i = res.begin(); i != res.end(); i++) {
       Row row = *i;
       user_str << row["user_id"] << "\n";
    }

    std::string user_string(user_str.str());

    return user_string;
}

/**
 * Get the list of all authorities who have submitted public keys.
 * @return a string containing all of the authorities' user IDs.
 */
std::string Database::get_pubkey_list(std::string procedure)
{
    query.reset();
    query << "SELECT user_id FROM is_authority WHERE proc_id = %0q";
    query.parse();

    Result res;

//     try {
    res = query.store(procedure);
//     } catch (...) {
//         return "";
//     }

    if (res.size() == 0) {
        return "";
    }

    Result::iterator i;
    std::stringstream key_str;

    for (i = res.begin(); i != res.end(); i++) {
        Row row = *i;
        key_str << row["user_id"];
        key_str << "\n";
    }

    std::string key_string(key_str.str());

    return key_string;
}

/**
 * Get the list of all authorities who have submitted public keys.
 * @return a string containing all of the authorities' user IDs.
 */
std::string Database::get_pubkey_list2(std::string procedure)
{
    query.reset();
    query << "SELECT user_id FROM is_authority WHERE proc_id = %0q";
    query.parse();

    Result res;

//     try {
    res = query.store(procedure);
//     } catch (...) {
//         return "";
//     }

    if (res.size() == 0) {
        return "";
    }

    Result::iterator i;
    std::stringstream key_str;

    for (i = res.begin(); i != res.end(); i++) {
        Row row = *i;
        key_str << row["user_id"];
        key_str << "\n";
    }

    std::string key_string(key_str.str());

    return key_string;
}

/**
 * Get the authorities' private keys.
 * @return a list of the private keys.
 */
std::vector<adder::ElgamalCiphertext> 
Database::get_priv_key_list(std::string procedure)
{
    Assert<Errors::Baduser> (user != "");
    Assert<Errors::Notauthority> (get_is_authority());
    Assert<Errors::Badauthstage> 
        (get_auth_stage(procedure, user) >= STAGE_WAITPOLYNOMIAL);

    query.reset();
    query << "SELECT value FROM auth_poly WHERE proc_id = %0q "
          << "AND auth_dest = %1q";
    query.parse();

    Result res;
    res = query.store(procedure, user);

    std::vector<adder::ElgamalCiphertext> priv_key_list;

    Result::iterator i;

    for (i = res.begin(); i != res.end(); i++) {
        Row row = *i;
        std::string priv_key_str(row["value"]);
        adder::ElgamalCiphertext priv_key;
        priv_key.from_str(priv_key_str);
        priv_key_list.push_back(priv_key);
    }

    query.reset();
    query << "UPDATE is_authority SET stage = 3 WHERE proc_id = %0q "
          << "AND user_id = %1q";
    query.parse();

    query.execute(procedure, user);

    return priv_key_list;
}

/**
 * Get the list of all users who have submitted votes.
 * @return a string containing all of the users' IDs.
 */
std::vector< std::pair<std::string, std::string> >
Database::get_vote_list(std::string procedure)
{
    query.reset();
    query << "SELECT user_id, time_stamp FROM choice WHERE proc_id = %0q";
    query.parse();

    Result res = query.store(procedure);

    Result::iterator i;

    std::vector< std::pair<std::string, std::string> > vote_vec;

    for (i = res.begin(); i != res.end(); i++) {
        Row row = *i;
        vote_vec.push_back(std::pair<std::string, std::string>
                           ("\"" + std::string(row["user_id"]) + "\"", 
                            "\"" + std::string(row["time_stamp"]) + "\""));
    }

    return vote_vec;
}

/**
 * Get the list of all users who have submitted votes.
 * @return a string containing all of the users' IDs.
 */
std::string Database::get_vote_list2(std::string procedure)
{
    query.reset();
    query << "SELECT user_id, time_stamp FROM choice WHERE proc_id = %0q";
    query.parse();

    Result res = query.store(procedure);

    if (res.size() == 0) {
        return "\n";
    }

    std::stringstream vote_str;
    Result::iterator i;

    for (i = res.begin(); i != res.end(); i++) {
        Row row = *i;
        vote_str << row["user_id"];
        vote_str << " ";
        vote_str << row["time_stamp"];
        vote_str << "\n";
    }

    std::string vote_string(vote_str.str());

    return vote_string;
}

/**
 * Returns the results in the form of a string.
 * @param proc_id the procedure ID.
 * @return a string containing the results.
 */
std::vector< std::pair<std::string, std::string> >
Database::get_results_str(std::string proc_id)
{
    query.reset();
    query << "SELECT * FROM result WHERE proc_id = %0q";
    query.parse();

    Result res = query.store(proc_id);

    std::stringstream results_str;
    Result::iterator i;

    std::vector< std::pair<std::string, std::string> > results_vec;

    for (i = res.begin(); i != res.end(); i++) {
        Row row = *i;

        query.reset();
        query << "SELECT * FROM proc_choice WHERE proc_id = %0q AND "
              << "choice_id = %1";
        query.parse();

        Result res2 = query.store(proc_id, std::string(row["choice_id"]));
        Result::iterator i2;
        i2 = res2.begin();
        Row row2 = *i2;

        results_vec.push_back(std::pair<std::string, std::string>
                           (std::string(row2["text"]), 
                            std::string(row["sum"])));
    }

    return results_vec;
}

/**
 * Returns the results in the form of a string.
 * @param proc_id the procedure ID.
 * @return a string containing the results.
 */
std::string Database::get_results_str2(std::string proc_id)
{
    query.reset();
    query << "SELECT * FROM result WHERE proc_id = %0q";
    query.parse();

    Result res = query.store(proc_id);

    if (res.size() == 0) {
        return "\n";
    }

    std::stringstream results_str;
    Result::iterator i;

    for (i = res.begin(); i != res.end(); i++) {
        Row row = *i;

        query.reset();
        query << "SELECT * FROM proc_choice WHERE proc_id = %0q "
              << "AND choice_id = %1";
        query.parse();

        Result res2 = query.store(proc_id, std::string(row["choice_id"]));

        Result::iterator i2;
        i2 = res2.begin();
        Row row2 = *i2;

        results_str << row2["text"];
        results_str << " ";
        results_str << row["sum"];
        results_str << "\n";
    }

    std::string results_string(results_str.str());

    return results_string;
}

/**
 * Returns the description of a procedure.
 * @param proc_id the procedure.
 * @return a string containing the description.
 */
std::string Database::get_description(std::string proc_id)
{
    query.reset();
    query << "SELECT text FROM proc WHERE proc_id = %0q";
    query.parse();

    Result res = query.store(proc_id);

    if (res.size() == 0) {
        return "";
    }

    Result::iterator i = res.begin();
    Row row = *i;

    std::string description_string(row["text"]);

    return description_string;
}

/**
 * Returns the title of a procedure.
 * @param proc_id the procedure.
 * @return a string containing the title.
 */
std::string Database::get_procedure_title(std::string proc_id)
{
    query.reset();
    query << "SELECT title FROM proc WHERE proc_id = %0q";
    query.parse();

    Result res = query.store(proc_id);

    if (res.size() == 0) {
        return "";
    }

    Result::iterator i = res.begin();
    Row row = *i;

    std::string title_string(row["title"]);

    return title_string;
}

/**
 * Returns a string containing the description of the election choices.
 * @return a string containing the description of the election choices.
 */
std::vector<std::string> Database::get_choices(std::string proc_id)
{
    query.reset();
    query << "SELECT * FROM proc_choice WHERE proc_id = %0q";
    query.parse();

    Result res = query.store(proc_id);

    Result::iterator i;

    std::vector<std::string> choices_vec;

    dont_quote_auto = true;
    for (i = res.begin(); i != res.end(); i++) {
        std::stringstream text_str;
        Row row = *i;
        text_str << row["text"];
        std::string text = text_str.str();
        //        text = text.substr(1, text.length() - 2);
        //        std::stringstream choice_str;
        //        choice_str << row["choice_id"] << "~" << text;
        choices_vec.push_back(text);
    }
    dont_quote_auto = false;

    return choices_vec;
}

/**
 * Returns a string containing the description of the election choices.
 * @return a string containing the description of the election choices.
 */
std::vector<std::string> Database::get_choices2(std::string proc_id)
{
    query.reset();
    query << "SELECT * FROM proc_choice WHERE proc_id = %0q";
    query.parse();

    Result res = query.store(proc_id);

    Result::iterator i;

    std::vector<std::string> choices_vec;

    for (i = res.begin(); i != res.end(); i++) {
        std::stringstream text_str;
        Row row = *i;
        text_str << row["text"];
        std::string text = text_str.str();
        text = text.substr(1, text.length() - 2);
        std::stringstream choice_str;
        choice_str << row["choice_id"] << "~" << text;
        choices_vec.push_back(choice_str.str());
    }

    return choices_vec;
}

/**
 * Gets the public key of an authority.
 * @param auth_id the user id of the authority.
 * @return the public key of the authority.
 */
adder::PublicKey Database::get_auth_pub_key(std::string procedure, std::string auth_id)
{
    query.reset();
    query << "SELECT public_key FROM is_authority "
          << "WHERE proc_id = %0q AND user_id = %1q";
    query.parse();

    Result res = query.store(procedure, auth_id);

    Assert<Errors::Empty> (res.size() == 1);

    Result::iterator i = res.begin();
    Row row = *i;

    std::string pub_key_str(row["public_key"]);
    adder::PublicKey pub_key(adder_ctx);

    try {
        pub_key.from_str(pub_key_str);
    } catch (adder::Invalid_key e) {
        ACE_DEBUG((LM_ERROR, "Error getting key: %s\n", ""));
        throw Errors::Empty();
    }

    return pub_key;
}

/**
 * Gets the stage of an authority.
 * @param auth_id the user id of the authority.
 * @return the stage of the authority.
 */
int Database::get_auth_stage(std::string procedure, std::string auth_id)
{
    query.reset();
    query << "SELECT stage FROM is_authority "
          << "WHERE proc_id = %0q AND user_id = %1q";
    query.parse();

    Result res = query.store(procedure, auth_id);

    Assert<Errors::Empty> (res.size() == 1);

    Result::iterator i = res.begin();
    Row row = *i;

    std::string stage_str(row["stage"]);

    return ACE_OS::atoi(stage_str.c_str());
}

/**
 * Get the authorities' public keys.
 * @return a list of the public keys.
 */
std::vector< std::pair<int, adder::PublicKey> > 
Database::get_auth_pub_keys(std::string procedure)
{
    query.reset();
    query << "SELECT number, public_key FROM is_authority "
          << "WHERE proc_id = %0q";
    query.parse();

    Result res = query.store(procedure);

    Result::iterator i;

    std::vector< std::pair<int, adder::PublicKey> > pub_keys;

    for (i = res.begin(); i != res.end(); i++) {
        Row row = *i;
        std::string key_string(row["public_key"]);
        int id = ACE_OS::atoi(row["number"]);

        if (!key_string.empty()) {
            try {
                adder::Context context(true);
                adder::PublicKey key(&context);
                key.from_str(key_string);
                std::pair<int, adder::PublicKey> p(id, key);
                //                p.first = id;
                //                p.second = key;
                pub_keys.push_back(p);
            }
            catch (...) {
                throw Errors::Critical();
            }
        }
    }

    return pub_keys;
}

/**
 * Get the authorities' public keys.
 * @return a list of the public keys.
 */
std::vector<std::string> Database::get_auth_pub_keys2(std::string procedure)
{
    query.reset();
    query << "SELECT number, public_key FROM is_authority "
          << "WHERE proc_id = %0q";
    query.parse();

    Result res = query.store(procedure);

    Result::iterator i;

    std::vector<std::string> pub_keys;

    for (i = res.begin(); i != res.end(); i++) {
        Row row = *i;
        std::string key_string(row["public_key"]);
        std::string id_string(row["number"]);

        if (!key_string.empty()) {
            pub_keys.push_back(id_string + " " + key_string);
        }
    }

    return pub_keys;
}

/**
 * Gets the encrypted vote of a user.
 * @param user_id the user id of the user.
 * @return the encrypted vote of the user.
 */
adder::Vote Database::get_vote(std::string procedure, std::string user_id)
{
    query.reset();
    query << "SELECT choice FROM choice WHERE proc_id = %0q "
          << "AND user_id = %1q";
    query.parse();

    Result res = query.store(procedure, user_id);

    Assert<Errors::Empty> (res.size() == 1);

    Result::iterator i = res.begin();
    Row row = *i;

    std::string vote_str(row["choice"]);
    adder::Vote vote;

    try {
        vote.from_str(vote_str);
    } catch (adder::Invalid_key e) {
        ACE_DEBUG((LM_ERROR, "Error loading vote: %s\n", ""));
        throw Errors::Empty();
    }

    return vote;
}

/**
 * Gets the ballot proof of a user.
 * @param user_id the user id of the user.
 * @return the ballot proof of the user.
 */
adder::VoteProof 
Database::get_ballot_proof(std::string procedure, std::string user_id)
{
    query.reset();
    query << "SELECT proof FROM choice WHERE proc_id = %0q "
          << "AND user_id = %1q";
    query.parse();

    Result res = query.store(procedure, user_id);

    Assert<Errors::Empty> (res.size() == 1);

    Result::iterator i = res.begin();
    Row row = *i;

    std::string proof_str(row["proof"]);
    adder::VoteProof proof;

    try {
        proof.from_str(proof_str);
    } catch (adder::Invalid_key e) {
        ACE_DEBUG((LM_ERROR, "Error loading proof: %s\n", ""));
        throw Errors::Empty();
    }

    return proof;
}

/**
 * Gets the short hash of a user.
 * @param user_id the user id of the user.
 * @return the short hash of the user.
 */
std::string Database::get_short_hash(std::string procedure, std::string user_id)
{
    query.reset();
    query << "SELECT short_hash FROM choice WHERE proc_id = %0q "
          << "AND user_id = %1q";
    query.parse();

    Result res = query.store(procedure,  user_id);

    Assert<Errors::Empty> (res.size() == 1);

    Result::iterator i = res.begin();
    Row row = *i;

    std::string hash_str(row["short_hash"]);

    return hash_str;
}

/**
 * Adds a vote for the user.
 * @param vote the vote to be added.
 */
void Database::add_vote(std::string procedure, adder::Vote vote, 
                        adder::VoteProof proof)
{
    Assert<Errors::Duplicate> (!already_voted(procedure));

    try {
        query.reset();
        query << "INSERT INTO choice "
              << "VALUES(%0q, %1q, %2q, %3q, %4q, NOW())"; // FIXME:
                                                           // Short
                                                           // hash wrong
        query.parse();

        query.execute(procedure, user, vote.str(), "SHORT HASH", proof.str());
    } catch (...) {
    }
}

/**
 * Insert an authority's polynomial into the database.
 * @param auth_id the "destination" authority's ID.
 * @param poly the polynomial.
 */
void Database::add_poly(std::string procedure, 
                        std::vector< std::pair<std::string, std::string> > 
                        &poly_vec)
{
    Assert<Errors::Badauthstage> (get_auth_stage(procedure, user) == STAGE_WAITKEYS);
    for (int j = 0; j < poly_vec.size(); j++) {
        query.reset();
        query << "SELECT user_id FROM is_authority WHERE proc_id = %0q "
              << "AND number = %1";
        query.parse();

        Result res = query.store(procedure, poly_vec[j].first);

        Assert<Errors::Empty> (res.size() == 1);
        
        Result::iterator i = res.begin();
        Row row = *i;
        
        std::string auth_name(row["user_id"]); // Destination authority.
        
        try {
            query.reset();
            query << "INSERT INTO auth_poly VALUES(%0q, %1q, %2q, %3q)";
            query.parse();

            query.execute(procedure, user, auth_name, poly_vec[j].second);
            
            query.reset();
            query << "UPDATE is_authority SET stage = 2 "
                  << "WHERE proc_id = %0q AND user_id = %1q";
            query.parse();

            query.execute(procedure, user);
        } catch (...) {
            throw Errors::Critical();
        }
    }
}

/**
 * Insert an authority's g-value into the database.
 * @param number the number.
 * @param value the value of g.
 */
void Database::add_gvalue(std::string procedure, 
                          std::vector< std::pair<int, std::string> > &gvalue_vec)
{
    query.reset();
    query << "INSERT INTO auth_g_values "
          << "VALUES(%0q, %1q, %2, %3q)";
    query.parse();

    for (int i = 0; i < gvalue_vec.size(); i++) {
        try {
            query.execute(procedure, user, gvalue_vec[i].first, 
                          gvalue_vec[i].second);
        } catch (...) {
            throw Errors::Critical();
        }
    }
}

/**
 * Adds a key for the user.
 * @param key the key to be added.
 */
void Database::add_key(std::string procedure, adder::PublicKey key)
{
    Assert<Errors::Duplicate> (!already_submitted_key(procedure));
    
    query.reset();
    query << "UPDATE is_authority SET public_key = %0q, "
          << "stage = 1 WHERE proc_id = %1q AND user_id = %2q";
    query.parse();

    query.execute(key.str(), procedure, user);
}

/**
 * Adds a partially-decrypted sum for the user.
 * @param sum the sum partial decryption to be added.
 */
void Database::add_sum(std::string procedure, std::vector<adder::Integer> sum_vec)
{
    Assert<Errors::Badauthstage> 
        (get_auth_stage(procedure, user) == STAGE_WAITGETPRIVKEYS);

    Assert<Errors::Duplicate> (!already_submitted_sum(procedure));

    try {
        std::string sum_str;
        
        for (unsigned int i = 0; i < sum_vec.size(); i++) {
            sum_str += sum_vec[i].str() + ' ';
        }
            
        query.reset();
        query << "INSERT INTO preresult VALUES (%0q, %1q, %2q)";
        query.parse();

        query.execute(procedure, user, sum_str);
            
        query.reset();
        query << "UPDATE is_authority SET stage = 7 "
              << "WHERE proc_id = %0q AND user_id = %1q";
        query.parse();
            
        query.execute(procedure, user);
    } catch (...) {
        throw Errors::Critical();
    }
}

/**
 * Sets the Adder Context.
 * @param ctx a pointer to the Adder context.
 */
void Database::set_context(adder::Context* ctx)
{
    adder_ctx = ctx;
}

/**
 * Set the procedure to which future requests over this connection will refer.
 * @param proc the procedure ID.
 * @return @b true if the procedure exists, @b false otherwise.
 */
bool Database::set_procedure(std::string proc)
{
    query.reset();
    query << "SELECT proc_id FROM proc WHERE proc_id = %0q";
    query.parse();

    Result res = query.store(proc);

    if (res.size() != 1) {
        return false;
    }

    procedure = proc;
    return true;
}

/**
 * Update the stage of the server for this procedure.
 * @param new_stage the stage to which the server should switch.
 * @param procedure the procedure.
 */
void Database::set_stage(std::string procedure, STAGE new_stage)
{
    query.reset();
    query << "UPDATE proc_data SET stage = %0 WHERE proc_id = %1q";
    query.parse();

    query.execute(new_stage, procedure);
}

/**
 * Sets the user ID.
 * @param user_id the user_id.
 */
void Database::set_user(std::string user_id)
{
    user = user_id;
}

/**
 * Gets the user ID.
 * @return the user_id.
 */
std::string Database::get_user()
{
    return user;
}

/**
 * Gets the authority's number.
 * @return the authority's number.
 */
int Database::get_auth_num(std::string procedure, std::string id)
{
    ACE_DEBUG((LM_DEBUG, "Getting authority number...\n"));

    query.reset();
    query << "SELECT number FROM is_authority "
          << "WHERE user_id = %0q AND proc_id = %1q";

    query.parse();

    Result res;
    try {
        res = query.store(id, procedure);
    } catch (...) {
        ACE_DEBUG((LM_ERROR, "Could not get authority number\n"));
        return 0;
    }

    if (res.size() != 1) {
        return false;
    }

    Result::iterator i = res.begin();
    Row row = *i;

    ACE_DEBUG((LM_DEBUG, "Authority is number: %d\n",
               ACE_OS::atoi(row["number"])));

    return ACE_OS::atoi(row["number"]);
}

int Database::get_auth_num(std::string procedure)
{
    return get_auth_num(procedure, user);
}

/**
 * Gets the authority status of the user.
 * @return @t true if the user is an authority, @b false otherwise.
 */
bool Database::get_is_authority()
{
    return is_authority;
}

/**
 * Generate the master key for this procedure.
 */
void Database::gen_master_key(std::string procedure, int length)
{
    // length is not being used right now
    ACE_UNUSED_ARG(length);

    adder::PublicKey master_key(adder_ctx);

    // XXX: why not stick this in a constant?
    master_key.make_partial_key(adder::Integer("125489087238195737954347303072014181609743210685664342148563282627702888711600616104630041189823615830151059574742027596462279644487544647092987402728428983866463990803061712929699319731954518354611104476983414003271056663266811843871036977620134268053541312343523587317149772597056898709288705318111363439959",
    10));
    //    master_key.make_partial_key(adder::Integer("51203"));

    try {
        query.reset();
        query << "INSERT INTO proc_masterkey VALUES(%0q, %1q, \"\")";
        query.parse();

        query.execute(procedure, master_key.str());
    } catch (...) {
    }
}

/**
 * Get the stage of the server for this procedure.
 * @param procedure the procedure.
 * @return the stage.
 */
STAGE Database::get_stage(std::string procedure)
{
    query.reset();
    query << "SELECT stage FROM proc_data WHERE proc_id = %0q";
    query.parse();
    Result res = query.store(procedure);
    
    if (res.size() != 1) { // FIXME: throw exception here?
        return STAGE_NONEXIST;
    }

    Result::iterator i = res.begin();
    Row row = *i;

    std::string stage_str(row["stage"]);

    return (STAGE)ACE_OS::atoi(stage_str.c_str());
}

/**
 * Get the ID of the procedure that is currently selected.
 * @return the procedure ID.
 */
std::string Database::get_procedure()
{
    return procedure;
}

/**
 * Get the authority threshold for the selected procedure.
 * @return the threshold.
 */
int Database::get_threshold(std::string procedure)
{
    query.reset();
    query << "SELECT threshold FROM proc WHERE proc_id = %0q";
    query.parse();

    Result res = query.store(procedure);

    Result::iterator i = res.begin();
    Row row = *i;

    std::string threshold_str(row["threshold"]);
    int threshold = ACE_OS::atoi(threshold_str.c_str());

    return threshold;
}

/**
 * Get the procedure creation time.
 *
 * @return the procedure creation time (in unix time)
 */
int Database::get_create_time(std::string procedure)
{
    query.reset();
    query << "SELECT create_time FROM proc WHERE proc_id = %0q";
    query.parse();

    Result res = query.store(procedure);

    Result::iterator i = res.begin();
    Row row = *i;

    std::string create_time_str(row["create_time"]);
    int create_time = ACE_OS::atoi(create_time_str.c_str());

    return create_time;
}

/**
 * Get the time allowed for voting.
 * @return the number of seconds voting will last.
 */
int Database::get_vote_time(std::string procedure)
{
    query.reset();
    query << "SELECT vote_time FROM proc WHERE proc_id = %0q";
    query.parse();

    Result res = query.store(procedure);

    Result::iterator i = res.begin();
    Row row = *i;

    std::string vote_time_str(row["vote_time"]);
    int vote_time = ACE_OS::atoi(vote_time_str.c_str());

    return vote_time;
}

/**
 * Get the time allowed for submitting public keys.
 * @return the number of seconds public key submission will last.
 */
int Database::get_public_key_time(std::string procedure)
{
    query.reset();
    query << "SELECT public_key_time FROM proc WHERE proc_id = %0q";
    query.parse();

    Result res = query.store(procedure);

    Result::iterator i = res.begin();
    Row row = *i;

    std::string public_key_time_str(row["public_key_time"]);
    int public_key_time = ACE_OS::atoi(public_key_time_str.c_str());

    return public_key_time;
}

/**
 * Get the time allowed for submitting polynomials.
 * @return the number of seconds polynomial submission will last.
 */
int Database::get_polynomial_time(std::string procedure)
{
    query.reset();
    query << "SELECT polynomial_time FROM proc WHERE proc_id = %0q";
    query.parse();

    Result res = query.store(procedure);

    Result::iterator i = res.begin();
    Row row = *i;

    std::string polynomial_time_str(row["polynomial_time"]);
    int polynomial_time = ACE_OS::atoi(polynomial_time_str.c_str());

    return polynomial_time;
}

/**
 * Get the time allowed for submitting secret keys.
 * @return the number of seconds secret key submission will last.
 */
int Database::get_secret_key_time(std::string procedure)
{
    query.reset();
    query << "SELECT secret_key_time FROM proc WHERE proc_id = %0q";
    query.parse();

    Result res = query.store(procedure);

    Result::iterator i = res.begin();
    Row row = *i;

    std::string secret_key_time_str(row["secret_key_time"]);
    int secret_key_time = ACE_OS::atoi(secret_key_time_str.c_str());

    return secret_key_time;
}

/**
 * Get the robustness factor.
 * @return the robustness factor.
 */
int Database::get_robustness(std::string procedure)
{
    query.reset();
    query << "SELECT robustness FROM proc WHERE proc_id = %0q";
    query.parse();

    Result res = query.store(procedure);

    Result::iterator i = res.begin();
    Row row = *i;

    std::string robustness_str(row["robustness"]);
    int robustness = ACE_OS::atoi(robustness_str.c_str());

    return robustness;
}

/**
 * Creates a new procedure.
 * @param id the procedure ID.
 * @param proc_info the procedure information.
 * @return true if successful, false otherwise.
 */
bool Database::create_procedure(std::string id, std::string title, 
                                std::string text, int threshold,
                                int publickeytime, int polynomialtime, int secretkeytime,
                                int votetime, int keylength, int robustness,
                                int minchoices, int maxchoices,
                                std::vector<std::string> choices_vec, 
                                std::vector<std::string> auths)
{
    ACE_DEBUG((LM_INFO, "Creating procedure %s...\n", id.c_str()));

    procedure = id;
    
    /* Ensure that the min choices and max choices fall in the
       appropriate range. */
    if (minchoices > maxchoices or maxchoices > choices_vec.size()) { 
        ACE_DEBUG((LM_ERROR, "Choices out of range\n"));
        return false;
    }

    std::vector<std::string>::iterator i;
    int j = 1;
    try {
        query.reset();
        query << "INSERT INTO is_authority VALUES(%0q, %1q, %2, \"\", 0)";
        query.parse();

        for (i = auths.begin(); i != auths.end(); i++, j++) {
            if (!query.execute(*i, id, j)) {
                ACE_DEBUG((LM_ERROR, "Could not insert into is_authority\n"));
                return false;
            }
        }
    } catch (...) {
        ACE_DEBUG((LM_ERROR, "Error inserting into is_authority\n"));
        throw Errors::Critical();
    }

    try {
        query.reset();
        query << "INSERT INTO proc "
              << "VALUES(%0q, %1q, %2q, %3, %4, %5, %6, %7, %8, NOW(), "
              << "NOW() * 2, 1024, %9, %10, %11)";
        query.parse();

        if (!query.execute(id, title, text, threshold,
                           int(time(0)), publickeytime, polynomialtime,
                           secretkeytime, votetime,
                           robustness, minchoices, maxchoices)) {
            return false;
        };

        query.reset();
        query << "INSERT INTO proc_data VALUES(%0q, 0)";
        query.parse();

        if (!query.execute(id)) {
            ACE_DEBUG((LM_ERROR, "Could not insert into proc_data\n"));
            return false;
        }
    } catch (...) {
        ACE_DEBUG((LM_ERROR, "Error inserting into proc_data\n"));
        throw Errors::Critical();
    }

    /* Generate master key info. */
    query.reset();
    query << "SELECT master_key_length FROM proc WHERE proc_id = %0q";
    query.parse();

    Result res = query.store(id);

    if (res.size() != 1) {
        ACE_DEBUG((LM_ERROR, "Value master_key_length not found\n"));
        return false;
    }

    Result::iterator k = res.begin();
    Row row = *k;

    std::string key_length_str(row["master_key_length"]);
    int key_length = ACE_OS::atoi(key_length_str.c_str());
    gen_master_key(procedure, key_length);

    /* Add choices. */
    adder::PublicKey master_key = get_master_key(procedure);
    adder::Integer p = master_key.get_p();
    std::vector<std::string>::iterator m;
    int num = 0;

    try {
        query.reset();
        query << "INSERT INTO proc_choice VALUES(%0q, %1, %2q)";
        query.parse();

        for (m = choices_vec.begin(); m != choices_vec.end(); m++, num++) {
            if (!query.execute(id, num, *m)) {
                ACE_DEBUG((LM_ERROR, "Could not add choice: %s\n", (*m).c_str()));
                return false;
            }
        }
    } catch (...) {
        throw Errors::Critical();
    }

    ACE_DEBUG((LM_INFO, "Successfully created procedure %s\n", id.c_str()));
    return true;
}

/**
 * Get the master key for this procedure.
 * @return the master key.
 */
adder::PublicKey Database::get_master_key(std::string procedure)
{
    query.reset();
    query << "SELECT master_key FROM proc_masterkey WHERE proc_id = %0q";
    query.parse();

    Result res = query.store(procedure);

    Assert<Errors::Empty> (res.size() == 1);

    Result::iterator i = res.begin();
    Row row = *i;

    std::string master_key_str(row["master_key"]);
    adder::PublicKey master_key(adder_ctx);

    try {
        master_key.from_str(master_key_str);
    } catch (adder::Invalid_key e) {
        ACE_DEBUG((LM_ERROR, "Error loading vote: %s\n", ""));
        throw Errors::Empty();
    }

    return master_key;
}

void Database::expire_public_key_timer(std::string procedure)
{
    if (get_stage(procedure) != STAGE_WAITKEYS) {
        return;
    }

    if (get_create_time(procedure) + get_polynomial_time(procedure) <= time(0)) {
        set_stage(procedure, STAGE_HALT);
        return;
    }

    if (get_authority_count(procedure) >= get_threshold(procedure) * get_robustness(procedure)) {
        PolynomialTimerHandler* timer = new PolynomialTimerHandler(get_procedure());
        int timeout = get_polynomial_time(procedure);
        ACE_Time_Value initial_delay(timeout);
        ACE_Reactor::instance()->schedule_timer(timer,
                                                0,
                                                initial_delay);
        set_stage(procedure, STAGE_WAITPOLYNOMIAL);
    } else {
        set_stage(procedure, STAGE_HALT);
    }
}

void Database::expire_polynomial_timer(std::string procedure)
{
    if (get_stage(procedure) != STAGE_WAITPOLYNOMIAL) {
        return;
    }

    if (get_create_time(procedure) + get_secret_key_time(procedure) <= time(0)) {
        set_stage(procedure, STAGE_HALT);
        return;
    }

    if (get_authority_count(procedure) >= get_threshold(procedure) * get_robustness(procedure)) {
        SecretKeyTimerHandler* timer = new SecretKeyTimerHandler(get_procedure());
        int timeout = get_secret_key_time(procedure);
        ACE_Time_Value initial_delay(timeout);
        ACE_Reactor::instance()->schedule_timer(timer,
                                                0,
                                                initial_delay);
        set_stage(procedure, STAGE_WAITGETPRIVKEYS);
    } else {
        set_stage(procedure, STAGE_HALT);
    }
}

void Database::expire_secret_key_timer(std::string procedure)
{
    if (get_stage(procedure) != STAGE_WAITGETPRIVKEYS) {
        return;
    }

    if (get_create_time(procedure) + get_vote_time(procedure) <= time(0)) {
        set_stage(procedure, STAGE_HALT);
        return;
    }

    if (get_authority_count(procedure) >= get_threshold(procedure) * get_robustness(procedure)) {
        set_stage(procedure, STAGE_COMPUTINGPUBKEY);
        aggregate_keys(procedure);

        ElectionTimerHandler* timer = new ElectionTimerHandler(get_procedure());
        int timeout = get_vote_time(procedure);
        ACE_Time_Value initial_delay(timeout);
        ACE_Reactor::instance()->schedule_timer(timer,
                                                0,
                                                initial_delay);
        set_stage(procedure, STAGE_VOTING);

    } else {
        set_stage(procedure, STAGE_HALT);
    }
}

void Database::expire_election_timer(std::string procedure)
{
    if (get_stage(procedure) != STAGE_VOTING) {
        return;
    }

    set_stage(procedure, STAGE_ADDCIPHER);
    compute_sum(procedure);
    set_stage(procedure, STAGE_WAITDECRYPT);
}

void Database::make_user(std::string username, std::string password,
                         std::string first_name, std::string middle_name,
                         std::string last_name, std::string email)
{
    query.reset();
    query << "SELECT * FROM users WHERE user_id = %0q";
    query.parse();
    
    Result res;
    try {
        res = query.store(SQLString(username));
    } catch (BadParamCount e) {
        std::cout << "Error: " << e.what() << std::endl;
        return;
    }

    ACE_DEBUG((LM_DEBUG, "Found %d match(es)\n", res.size()));
    
    if (res.size() != 0) { // User exists already.
        throw Errors::Duplicate();
    }
    
    std::string salt("0");

    query.reset();
    query << "INSERT INTO users VALUES(%0q, %1q, %2q, %3q, %4q, %5q, %6q, 0, NULL, NULL)";
    query.parse();
    
    query.execute(username, password, first_name, middle_name, 
                  last_name, email, salt);
}

bool Database::progress_procedure(std::string procedure)
{
    switch (get_stage(procedure)) {
    case STAGE_WAITKEYS:
        expire_public_key_timer(procedure);
        break;
    case STAGE_WAITPOLYNOMIAL:
        expire_polynomial_timer(procedure);
        break;
    case STAGE_WAITGETPRIVKEYS:
        expire_secret_key_timer(procedure);
        break;
    case STAGE_VOTING:
        expire_election_timer(procedure);
        break;
    case STAGE_HALT:
        return false;
    default:
        break;
    }

    return true;
}

/**
 * Deletes a procedure.
 */
void Database::delete_procedure(std::string procedure)
{
    query.reset();
    query << "DELETE FROM is_authority WHERE proc_id = %0q";
    query.parse();

    query.execute(procedure);

    query.reset();
    query << "DELETE FROM auth_poly WHERE proc_id = %0q";
    query.parse();
    query.execute(procedure);

    query.reset();
    query << "DELETE FROM auth_g_values WHERE proc_id = %0q";
    query.parse();
    query.execute(procedure);

    query.reset();
    query << "DELETE FROM proc WHERE proc_id = %0q";
    query.parse();
    query.execute(procedure);

    query.reset();
    query << "DELETE FROM proc_data WHERE proc_id = %0q";
    query.parse();
    query.execute(procedure);

    query.reset();
    query << "DELETE FROM choice WHERE proc_id = %0q";
    query.parse();
    query.execute(procedure);

    query.reset();
    query << "DELETE FROM proc_choice WHERE proc_id = %0q";
    query.parse();
    query.execute(procedure);

    query.reset();
    query << "DELETE FROM proc_pubkey WHERE proc_id = %0q";
    query.parse();
    query.execute(procedure);

    query.reset();
    query << "DELETE FROM proc_masterkey WHERE proc_id = %0q";
    query.parse();
    query.execute(procedure);

    query.reset();
    query << "DELETE FROM cipher_result WHERE proc_id = %0q";
    query.parse();
    query.execute(procedure);

    query.reset();
    query << "DELETE FROM preresult WHERE proc_id = %0q";
    query.parse();
    query.execute(procedure);

    query.reset();
    query << "DELETE FROM pubkey WHERE proc_id = %0q";
    query.parse();
    query.execute(procedure);

    query.reset();
    query << "DELETE FROM result WHERE proc_id = %0q";
    query.parse();
    query.execute(procedure);
}

/**
 * Initialize the database values for the specified procedure.
 * @param proc the procedure ID.
 * @return @b true if successful, @b false otherwise.
 */
bool Database::start_procedure(std::string procedure)
{
    ACE_DEBUG((LM_DEBUG, "Starting procedure %s\n", procedure.c_str()));

    /* Clear the polynomials for this procedure. */
    query.reset();
    query << "DELETE FROM auth_poly WHERE proc_id = %0q";
    query.parse();
    query.execute(procedure);

    /* Clear the g-values for this procedure. */
    query.reset();
    query << "DELETE FROM auth_g_values WHERE proc_id = %0q";
    query.parse();
    
    query.execute(procedure);
        
    query.reset();
    query << "UPDATE is_authority SET public_key = \"\" WHERE proc_id = %0q";
    query.parse();
    query.execute(procedure);

    query.reset();
    query << "UPDATE is_authority SET stage = 0 WHERE proc_id = %0q";
    query.parse();
    query.execute(procedure);

    /* Zero the authority count and set stage for this procedure. */
    query.reset();
    query << "UPDATE proc_data SET stage = 1"
          << " WHERE proc_id = %0q";
    query.parse();
    query.execute(procedure);

    /* Clear the encrypted choices for this procedure. */
    query.reset();
    query << "DELETE FROM choice WHERE proc_id = %0q";
    query.parse();
    query.execute(procedure);

    /* Clear the public keys for this procedure. */
    query.reset();
    query << "DELETE FROM proc_pubkey WHERE proc_id = %0q";
    query.parse();
    query.execute(procedure);

    /* Clear the master key and polynomial for this procedure. */
    /*query << "DELETE FROM proc_masterkey WHERE proc_id = \""
          << procedure << "\"";
    query.parse();
    query.execute(procedure)*/

    /* Clear the encrypted totals for this procedure. */
    query.reset();
    query << "DELETE FROM cipher_result WHERE proc_id = %0q";
    query.parse();
    query.execute(procedure);

    /* Clear the partially-decrypted sums for this procedure. */
    query.reset();
    query << "DELETE FROM preresult WHERE proc_id = %0q";
    query.parse();
    query.execute(procedure);

    /* Clear the final (plaintext) results for this procedure. */
    query.reset();
    query << "DELETE FROM result WHERE proc_id = %0q";
    query.parse();
    query.execute(procedure);

    /* Clear the master public key for this procedure. */
    query.reset();
    query << "DELETE FROM pubkey WHERE proc_id = %0q";
    query.parse();
    query.execute(procedure);

    /* Update the procedure creation time to the start time. */
    query.reset();
    query << "UPDATE proc SET create_time = %1 WHERE proc_id = %1q";
    query.parse();
    query.execute(int(time(0)), procedure);

    if (get_create_time(procedure) + get_public_key_time(procedure) <= time(0)) {
	set_stage(procedure, STAGE_HALT);
        return true;
    }
 
    PublicKeyTimerHandler* timer = new PublicKeyTimerHandler(get_procedure());
    int timeout = get_public_key_time(procedure);
    ACE_Time_Value initial_delay(timeout);
    ACE_Reactor::instance()->schedule_timer(timer, 0, initial_delay);
    set_stage(procedure, STAGE_WAITKEYS);

    return true;
}
