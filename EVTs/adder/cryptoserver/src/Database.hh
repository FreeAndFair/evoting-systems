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
 * @file Database.hh
 * Interface of the Database class.
 */

#ifndef DATABASE_HH
#define DATABASE_HH

#include <string>

#include "mysql++.h"

#include "PublicKey.h"
#include "Vote.h"
#include "VoteProof.h"

using namespace mysqlpp;

/**
 * Possible stages of the procedure.
 */
enum STAGE {
    STAGE_NOTSTARTED, /**< Procedure has not yet been started. */
    STAGE_WAITKEYS, /**< Waiting for the public keys of the authorities. */
    STAGE_WAITPOLYNOMIAL, /**< Waiting for the authorities to submit their polynomial data. */
    STAGE_WAITGETPRIVKEYS, /**< Waiting for authorities to get their privkey data. */
    STAGE_COMPUTINGPUBKEY, /**< Computing the public key. */
    STAGE_VOTING, /**< Inside the voting process. */
    STAGE_ADDCIPHER, /**< Sums the votes to get the cipher sum. */
    STAGE_WAITDECRYPT, /**< Waiting for the authorities to submit their decryptions. */
    STAGE_DECRYPTING, /**< Waiting for the system to decrypt the result. */
    STAGE_FINISHED, /**< The election is finished and the result has been posted. */
    STAGE_HALT, /**< An error has occurred and the election cannot continue. */
    STAGE_NONEXIST, /**< This procedure does not exist. */
};

/**
 * Acts as a wrapper for the lower-level database functions.  This
 * currently uses MySQL++, but it is intended to allow transparent
 * replacement of database systems.
 */
class Database
{
public:
    Database();
    ~Database();

    bool authenticate(std::string user_id, std::string password,
                      std::string &authority, std::string &session_id,
                      std::string procedure_id);
    bool authenticate(std::string session_id, std::string &user_id,
                      std::string &authority, std::string procedure_id);

    std::string create_session_id(std::string user_id);

    bool logout(std::string session_id);

    bool already_voted(std::string proc_id);
    bool already_submitted_key(std::string proc_id);
    bool already_submitted_sum(std::string proc_id);

    bool procedure_exists(std::string proc_id);

    void compute_sum(std::string proc_id);
    void aggregate_keys(std::string proc_id);
    void decrypt_sum(std::string proc_id);
    void post_results(std::vector<adder::Integer> results);

    void add_vote(std::string proc_id, adder::Vote vote, adder::VoteProof proof);
    void add_key(std::string proc_id, adder::PublicKey pub_key);
    void add_poly(std::string proc_id, 
                  std::vector< std::pair<std::string, std::string> > &poly_vec);
    void add_gvalue(std::string proc_id,
                    std::vector< std::pair<int, std::string> > &gvalue_vec);
    void add_sum(std::string proc_id, std::vector<adder::Integer> sum_vec);

    void set_context(adder::Context* ctx);
    bool set_procedure(std::string proc);
    void set_user(std::string user_id);

    bool open(std::string db, std::string host, std::string user,
              std::string password, int port);
    void close();

    std::string get_user();
    bool get_is_authority();
    int get_auth_num(std::string proc_id);
    int get_auth_num(std::string proc_id, std::string id);
    adder::Vote get_sum(std::string proc_id);
    int get_num_voters();
    int get_num_choices(std::string proc_id);
    int get_min_choices(std::string proc_id);
    int get_max_choices(std::string proc_id);
    std::string get_base(std::string proc_id);
    std::string get_num_votes(std::string proc_id);
    std::string get_procedure_list();
    std::string get_procedure_list2();
    std::string get_user_list();
    std::string get_user_list2();
    std::string get_pubkey_list(std::string proc_id);
    std::string get_pubkey_list2(std::string proc_id);
    std::vector< std::pair<std::string, std::string> >
    get_vote_list(std::string proc_id);
    std::string get_vote_list2(std::string proc_id);
    std::vector< std::pair<std::string, std::string> > get_results_str(std::string proc_id);
    std::string get_results_str2(std::string proc_id);
    std::string get_description(std::string proc_id);
    std::string get_procedure_title(std::string proc_id);
    std::vector<std::string> get_choices(std::string proc_id);
    std::vector<std::string> get_choices2(std::string proc_id);
    std::vector<adder::ElgamalCiphertext> get_priv_key_list(std::string proc_id);
    adder::PublicKey get_auth_pub_key(std::string procedure, std::string auth_id);
    int get_auth_stage(std::string procedure, std::string auth_id);
    std::vector< std::pair<int, adder::PublicKey> > get_auth_pub_keys(std::string 
                                                                      proc_id);
    std::vector<std::string> get_auth_pub_keys2(std::string proc_id);
    adder::Vote get_vote(std::string proc_id, std::string user_id);
    adder::VoteProof get_ballot_proof(std::string proc_id, std::string user_id);
    std::string get_short_hash(std::string proc_id, std::string user_id);
    adder::PublicKey get_pub_key(std::string proc_id);
    int get_authority_count(std::string proc_id);
    STAGE get_stage(std::string proc_id);
    std::string get_procedure();
    int get_threshold(std::string proc_id);
    int get_remaining_authorities(std::string proc_id);

    void delete_procedure(std::string proc);
    bool start_procedure(std::string proc);

    int get_create_time(std::string proc);
    int get_public_key_time(std::string proc);
    int get_polynomial_time(std::string proc);
    int get_secret_key_time(std::string proc);
    int get_vote_time(std::string proc);

    int get_robustness(std::string proc_id);

    bool create_procedure(std::string id, std::string title, 
                          std::string text, int threshold,
                          int pubkey_time, int poly_time, int seckey_time,
                          int vote_time, int key_length, int robustness,
                          int minchoices, int maxchoices,
                          std::vector<std::string> choices, 
                          std::vector<std::string> auths);

    void set_stage(std::string proc_id, STAGE new_stage);
    adder::PublicKey get_master_key(std::string proc_id);

    void expire_public_key_timer(std::string proc_id);
    void expire_polynomial_timer(std::string proc_id);
    void expire_secret_key_timer(std::string proc_id);
    void expire_election_timer(std::string proc_id);

    void make_user(std::string username, std::string password, 
                   std::string first_name, std::string middle_name,
                   std::string last_name, std::string email);

    bool progress_procedure(std::string proc_id);

private:
    Connection conn; /**< Object to represent the database connection. */
    std::string user; /**< The username of the current cryptoserver user. */
    bool is_authority; /**< True if the user is an authority. */
    Query query; /**< Query object. */
    adder::Context* adder_ctx; /**< The context for libadder functions. */
    std::string procedure; /**< The name of the currently selected procedure. */

    void gen_master_key(std::string proc_id, int length);
    void gen_base(std::string proc_id, int choices);
};

namespace Errors {
    struct Badauthstage {};
    struct Badsession {};
    struct Badstage {};
    struct Baduser {};
    struct Duplicate {};
    struct Empty {};
    struct Invalidproof {};
    struct Notauthority {};
   
    struct Critical {};
}

#endif /* DATABASE_HH */
