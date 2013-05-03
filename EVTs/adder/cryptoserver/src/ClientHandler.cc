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
 * @file ClientHandler.cc
 * Interface of the ClientHandler class.
 */

#include <sstream>
#include <cstring>

#include <boost/spirit/core.hpp>
#include <boost/spirit/utility/regex.hpp>
#include <boost/lambda/core.hpp>
#include <boost/lambda/lambda.hpp>
#include <boost/regex.hpp>

#include "ace/Acceptor.h"
#ifdef ENABLE_SSL
#include "ace/SSL/SSL_SOCK_Acceptor.h"
#else
#include "ace/SOCK_Acceptor.h"
#endif
#include "ace/UUID.h"

#include "exceptions.h"

#include "ClientHandler.hh"
#include "Database.hh"
#include "ElectionTimeoutHandler.hh"
#include "Utilities.hh"
#include "Options.hh"

using namespace boost;

#ifdef ENABLE_SSL
template class ACE_Acceptor<ClientHandler, ACE_SSL_SOCK_ACCEPTOR>;
#else
template class ACE_Acceptor<ClientHandler, ACE_SOCK_ACCEPTOR>;
#endif

std::map<std::string, PClientHandler_mem> ClientHandler::function_map;

const int BUFSIZE = 100 * 1024;

/**
 * Constructor.
 */
ClientHandler::ClientHandler()
    : adder_ctx(true)
{
    if (!database.open(OPTIONS->db_database, OPTIONS->db_hostname,
                       OPTIONS->db_username, OPTIONS->db_password,
                       OPTIONS->db_port)) {
        close(0);
        return;
    }

    database.set_context(&adder_ctx);

    getting_polylist = false;
    getting_gvaluelist = false;
    getting_key = false;
    getting_vote = false;
    getting_sum = false;
    getting_createprocedure = false;

    is_admin = false;
}

/**
 * Destructor.
 */
ClientHandler::~ClientHandler()
{

}

/**
 * Removes us from the reactor.
 */
void ClientHandler::destroy()
{
    /* Remove the handler from the reactor. The DONT_CALL flag prevents
     * handle_close() from being called, since that is most likely what
     * is calling the current method. This will avoid infinite loopage */
    ACE_Reactor::instance()->remove_handler(this,
                                            ACE_Event_Handler::READ_MASK
                                            | ACE_Event_Handler::DONT_CALL);

    /* Delete the current handler object. */
    delete this;
}

/**
 * Called when a new client connetion has been accepted.
 * @param void_acceptor pointer to the acceptor.
 * @return 0 if we can successfully run in detached mode, -1 otherwise.
 */
int ClientHandler::open(void* void_acceptor)
{
    /* Stores the address of the client. */
    ACE_INET_Addr addr;

    /* Try to fetch the client's address information. If we fail, then
     * return an error. */
    if (peer().get_remote_addr(addr) == -1) {
        return -1;
    }

    /* Create a local variable to store the acceptor, and cast. */
#ifdef ENABLE_SSL
    ACE_Acceptor<ClientHandler, ACE_SSL_SOCK_ACCEPTOR> *acceptor = 
        (ACE_Acceptor<ClientHandler, ACE_SSL_SOCK_ACCEPTOR>*)void_acceptor;
#else
    ACE_Acceptor<ClientHandler, ACE_SOCK_ACCEPTOR> *acceptor = 
        (ACE_Acceptor<ClientHandler, ACE_SOCK_ACCEPTOR>*)void_acceptor;
#endif

    ACE_UNUSED_ARG(acceptor);

    return activate(THR_DETACHED);
}

/**
 * Closes the handler. This just passes the buck to the destroy()
 * method.
 * @param flags the flags.
 * @return always returns 0.
 */
int ClientHandler::close(u_long flags)
{
    ACE_UNUSED_ARG(flags);

    /* Pass the buck. */
    destroy();

    return 0;
}

/**
 * This method maybe should be deleted. Let's think about it...
 */
int ClientHandler::handle_close(ACE_HANDLE handler,
                                 ACE_Reactor_Mask mask)
{
    ACE_UNUSED_ARG(handler);
    ACE_UNUSED_ARG(mask);

    destroy();
    return 0;
}

/**
 * The main function of the client handler thread.
 * @return -1 if the client has disconnected, 0 otherwise.
 */
int ClientHandler::svc(void)
{
    char buf[BUFSIZE];

    while (1) {
        if (process(buf, sizeof(buf)) == -1) {
            return -1;
        }
    }

    return 0;
}

/**
 * Counts the number of character in the message and sends it.
 * @param message the message to be send.
 */
void ClientHandler::send_msg(std::string message)
{
    ACE_DEBUG((LM_DEBUG, "sending message:%s", message.c_str()));
    peer().send(message.c_str(), message.size());
}

/**
 * Sends the private key list to the client.
 */
void ClientHandler::send_priv_key_list(std::string procedure)
{
    try {
        std::vector<adder::ElgamalCiphertext> priv_keys = 
            database.get_priv_key_list(procedure);

        send_msg("BEGIN PRIVKEYLIST\n");
        
        for (unsigned int i = 0; i < priv_keys.size(); i++) {
            send_msg(priv_keys[i].str() + "\n");
        }
        
        send_msg("END PRIVKEYLIST\n");
    } catch (Errors::Baduser) {
        send_msg("GETPRIVKEYLIST BADUSER\n");
    } catch (Errors::Notauthority) {
        send_msg("GETPRIVKEYLIST NOTAUTHORITY\n");
    } catch (Errors::Badauthstage) {
        send_msg("GETPRIVKEYLIST BADAUTHSTAGE\n");
    }
}

/**
 * Send the choices list to the client.
 * @param proc_id the procedure ID.
 */
void ClientHandler::send_choices(std::string proc_id)
{
    std::vector<std::string> choices_vec = database.get_choices2(proc_id);

    send_msg("BEGIN CHOICES\n");

    for (unsigned int i = 0; i < choices_vec.size(); i++) {
        send_msg(choices_vec[i] + "\n");
    }

    send_msg("END CHOICES\n");
}

/**
 * Sends the list of authorities' public keys to the client.
 */
void ClientHandler::send_auth_pub_keys(std::string procedure)
{
    std::vector<std::string> auth_pub_keys;

    //    try {
    auth_pub_keys = database.get_auth_pub_keys2(procedure);
    //    } catch (...) {
    //        return;
    //    }

    send_msg("BEGIN AUTHPUBKEYS\n");

    for (unsigned int i = 0; i < auth_pub_keys.size(); i++) {
        send_msg(auth_pub_keys[i] + "\n");
    }

    send_msg("END AUTHPUBKEYS\n");
}

void ClientHandler::initialize_function_map()
{
    function_map["ADMIN"] = &ClientHandler::admin_function;
    function_map["CREATEPROCEDURE"] = &ClientHandler::createprocedure_function;
    function_map["DELETEPROCEDURE"] = &ClientHandler::deleteprocedure_function;
    function_map["GETAUTHPUBKEY"] = &ClientHandler::getauthpubkey_function;
    function_map["GETAUTHPUBKEYS"] = &ClientHandler::getauthpubkeys_function;
    function_map["GETAUTHSTAGE"] = &ClientHandler::getauthstage_function;
    function_map["GETBALLOTPROOF"] = &ClientHandler::getballotproof_function;
    function_map["GETCHOICES"] = &ClientHandler::getchoices_function;
    function_map["GETDESCRIPTION"] = &ClientHandler::getdescription_function;
    function_map["GETKEYCONSTANTS"] = &ClientHandler::getkeyconstants_function;
    function_map["GETNUMCHOICES"] = &ClientHandler::getnumchoices_function;
    function_map["GETNUMVOTES"] = &ClientHandler::getnumvotes_function;
    function_map["GETPRIVKEYLIST"] = &ClientHandler::getprivkeylist_function;
    function_map["GETPROCEDURELIST"] = &ClientHandler::getprocedurelist_function;
    function_map["GETPUBKEY"] = &ClientHandler::getpubkey_function;
    function_map["GETPUBKEYLIST"] = &ClientHandler::getpubkeylist_function;
    function_map["GETREMAINING"] = &ClientHandler::getremaining_function;
    function_map["GETRESULTS"] = &ClientHandler::getresults_function;
    function_map["GETSHORTHASH"] = &ClientHandler::getshorthash_function;
    function_map["GETSTAGE"] = &ClientHandler::getstage_function;
    function_map["GETSUM"] = &ClientHandler::getsum_function;
    function_map["GETTHRESHOLD"] = &ClientHandler::getthreshold_function;
    function_map["GETTIMES"] = &ClientHandler::gettimes_function;
    function_map["GETTITLE"] = &ClientHandler::gettitle_function;
    function_map["GETUSERLIST"] = &ClientHandler::getuserlist_function;
    function_map["GETVOTE"] = &ClientHandler::getvote_function;
    function_map["GETVOTELIST"] = &ClientHandler::getvotelist_function;
    function_map["MAKEUSER"] = &ClientHandler::makeuser_function;
    function_map["PROGRESSPROCEDURE"] = &ClientHandler::progressprocedure_function;
    function_map["SENDPOLYLIST"] = &ClientHandler::sendpolylist_function;
    function_map["SENDPUBLICKEY"] = &ClientHandler::sendpublickey_function;
    function_map["SENDSUM"] = &ClientHandler::sendsum_function;
    function_map["SENDVOTE"] = &ClientHandler::sendvote_function;
    function_map["SESSION"] = &ClientHandler::session_function;
    function_map["STARTPROCEDURE"] = &ClientHandler::startprocedure_function;
    function_map["STOPPROCEDURE"] = &ClientHandler::stopprocedure_function;
    function_map["USER"] = &ClientHandler::user_function;
    function_map["VERSION"] = &ClientHandler::version_function;

    /* Old functions for PHP compatibility. */
    function_map["GETAUTHPUBKEYS2"] = &ClientHandler::getauthpubkeys2_function;
    function_map["GETCHOICES2"] = &ClientHandler::getchoices2_function;
    function_map["GETPROCEDURELIST2"] = &ClientHandler::getprocedurelist2_function;
    function_map["GETPRIVKEYLIST2"] = &ClientHandler::getprivkeylist2_function;
    function_map["GETPUBKEYLIST2"] = &ClientHandler::getpubkeylist2_function;
    function_map["GETRESULTS2"] = &ClientHandler::getresults2_function;
    function_map["GETTIMES2"] = &ClientHandler::gettimes2_function;
    function_map["GETUSERLIST2"] = &ClientHandler::getuserlist2_function;
    function_map["GETVOTELIST2"] = &ClientHandler::getvotelist2_function;
}

void ClientHandler::admin_function(std::string arguments)
{
    boost::regex e("\\s*\"(.*?)\"\\s*");
    boost::smatch match;

    bool parsed = boost::regex_match(arguments, match, e);
    
    if (!parsed) {
        send_msg("BADCOMMAND\n");
    } else {
        std::string password(match[1].first, match[1].second);

        if (!OPTIONS->admin || password == OPTIONS->admin_password) {
            is_admin = true;
            send_msg("ADMIN OK\n");
        } else {
            send_msg("ADMIN BADPASSWORD\n");
        }
    }
}

/**
 * Processes a procedure creation request..
 * @param tokens the tokenized message.
 */
void ClientHandler::createprocedure_function(std::string arguments)
{
    boost::regex e("\\s*\"(.*?)\"\\s*"
                   "\\s*\"(.*?)\"\\s*"
                   "\\s*(\\d+)\\s*"
                   "\\s*(\\d+)\\s*"
                   "\\s*(\\d+)\\s*"
                   "\\s*(\\d+)\\s*"
                   "\\s*(\\d+)\\s*"
                   "\\s*(\\d+)\\s*"
                   "\\s*(\\d+)\\s*"
                   "\\s*(\\d+)\\s*"
                   "\\s*(\\d+)\\s*"
                   "\\s*\\((.*)\\)\\s*"
                   "\\s*\\((.*)\\)\\s*");
    boost::smatch match;

    bool parsed_expr = boost::regex_match(arguments, match, e);

    if (!parsed_expr) {
        send_msg("BADCOMMAND\n");
    } else {
        std::string title(match[1].first, match[1].second);
        std::string text(match[2].first, match[2].second);
        int threshold(ACE_OS::atoi(std::string(match[3].first, match[3].second).c_str()));
        int pubkey_time(ACE_OS::atoi(std::string(match[4].first, match[4].second).c_str()));
        int poly_time(ACE_OS::atoi(std::string(match[5].first, match[5].second).c_str()));
        int seckey_time(ACE_OS::atoi(std::string(match[6].first, match[6].second).c_str()));
        int vote_time(ACE_OS::atoi(std::string(match[7].first, match[7].second).c_str()));
        int key_length(ACE_OS::atoi(std::string(match[8].first, match[8].second).c_str()));
        int robustness(ACE_OS::atoi(std::string(match[9].first, match[9].second).c_str()));
        int minchoices(ACE_OS::atoi(std::string(match[10].first, match[10].second).c_str()));
        int maxchoices(ACE_OS::atoi(std::string(match[11].first, match[11].second).c_str()));

        std::string choices_str(match[12].first, match[12].second);
        std::string auths_str(match[13].first, match[13].second);

        std::vector<std::string> choices;
        std::vector<std::string> auths;
        
        std::string tmp_choice, tmp_auth;

        bool parsed_choices = spirit::parse(choices_str.c_str(),
                                            (spirit::regex_p("\".*?\"")
                                             [spirit::assign_a(tmp_choice)])
                                            [spirit::push_back_a(choices, tmp_choice)] % ',',
                                            spirit::space_p).full;

        bool parsed_auths = spirit::parse(auths_str.c_str(),
                                          (spirit::regex_p("\".*?\"")
                                           [spirit::assign_a(tmp_auth)])
                                          [spirit::push_back_a(auths, tmp_auth)] % ',',
                                          spirit::space_p).full;

        if (!parsed_choices || !parsed_auths) {
            send_msg("BADCOMMAND\n");
        } else {
            /* Erase quotes. */
            unsigned int i;
            for (i = 0; i < choices.size(); i++) {
                choices[i].erase(0, 1);
                choices[i].erase(choices[i].length()-1, 1);
            }

            for (i = 0; i < auths.size(); i++) {
                auths[i].erase(0, 1);
                auths[i].erase(auths[i].length()-1, 1);
            }

            /*
             * MySQL has its own UUID() function, but this allows us to support other
             * databases as well.
             */
            ACE_Utils::UUID* uuid = ACE_Utils::UUID_GENERATOR::instance()->generateUUID();
            std::string uuid_str(uuid->to_string()->c_str());

            delete uuid;

            ACE_DEBUG((LM_DEBUG, "creating procedure: %s\n", uuid_str.c_str()));

            if (!is_admin) {
                send_msg("CREATEPROCEDURE NOTADMIN\n");
            } else if (database.procedure_exists(uuid_str)) {
                throw Errors::Critical();
            } else {
                bool proc_error = database.create_procedure(uuid_str, title, 
                                                            text,  threshold,
                                                            pubkey_time,  poly_time,  seckey_time,
                                                            vote_time,  key_length,  robustness,
                                                            minchoices, maxchoices,
                                                            choices, 
                                                            auths);
                if (proc_error) {
                    send_msg("CREATEPROCEDURE OK\n");
                } else {
                    send_msg("CREATEPROCEDURE FAILURE\n");
                }
            }
        }
    }
}

void ClientHandler::deleteprocedure_function(std::string arguments)
{
    std::string procedure;

    bool parsed = spirit::parse(arguments.c_str(),
                                '\"' >> 
                                (*(spirit::alnum_p | '-'))
                                 [spirit::assign_a(procedure)]
                                >> '\"',
                                spirit::space_p).full;

    if (!parsed) {
        send_msg("BADCOMMAND\n");
    } else if (!is_admin) {
        send_msg("DELETEPROCEDURE NOTADMIN\n");
    } else if (!database.procedure_exists(procedure)) {
        send_msg("DELETEPROCEDURE BADPROCEDURE\n");
    } else {
        database.delete_procedure(procedure);
        send_msg("DELETEPROCEDURE OK\n");
    }
}

void ClientHandler::getauthpubkeys_function(std::string arguments)
{
    std::string procedure;

    bool parsed = spirit::parse(arguments.c_str(),
                                '\"' >> 
                                (*(spirit::alnum_p | '-'))
                                 [spirit::assign_a(procedure)]
                                >> '\"',
                                spirit::space_p).full;

    if (!parsed) {
        send_msg("BADCOMMAND\n");
    } else if (!database.procedure_exists(procedure)) {
        send_msg("GETAUTHPUBKEYS BADPROCEDURE\n");
    } else if (database.get_stage(procedure) < STAGE_WAITPOLYNOMIAL) {
        send_msg("GETAUTHPUBKEYS BADSTAGE\n");
    } else {
        std::vector< std::pair<int, adder::PublicKey> > pub_keys;
        pub_keys = database.get_auth_pub_keys(procedure);
        
        std::stringstream key_str;
        key_str << "(";
        
        std::vector< std::pair<int, adder::PublicKey> >::iterator i;
        for (i = pub_keys.begin(); i != pub_keys.end(); i++) {
            key_str << "(" << i->first << "," 
                    << i->second.str() << "),";
        }
        
        std::string key_string(key_str.str());
        key_string.erase(key_string.length() - 1);
        
        key_string += ')';
        
        send_msg("GETAUTHPUBKEYS " + key_string + '\n');
    }
}

void ClientHandler::getauthpubkeys2_function(std::string arguments)
{
    std::string procedure;

    bool parsed = spirit::parse(arguments.c_str(),
                                '\"' >> 
                                (*(spirit::alnum_p | '-'))
                                 [spirit::assign_a(procedure)]
                                >> '\"',
                                spirit::space_p).full;

    if (!parsed) {
        send_msg("BADCOMMAND\n");
    } else if (!database.procedure_exists(procedure)) {
        send_msg("GETAUTHPUBKEYS BADPROCEDURE\n");
    } else if (database.get_stage(procedure) < STAGE_WAITPOLYNOMIAL) {
        send_msg("GETAUTHPUBKEYS BADSTAGE\n");
    } else {
        send_auth_pub_keys(procedure);
    }
}

void ClientHandler::getchoices_function(std::string arguments)
{
    std::string procedure;

    bool parsed = spirit::parse(arguments.c_str(),
                                '\"' >> 
                                (*(spirit::alnum_p | '-'))
                                 [spirit::assign_a(procedure)]
                                >> '\"',
                                spirit::space_p).full;

    if (!parsed) {
        send_msg("BADCOMMAND\n");
    } else if (!database.procedure_exists(procedure)) {
        send_msg("GETCHOICES BADPROCEDURE\n");
    } else {
        std::vector<std::string> choices_vec = database.get_choices(procedure);

        std::stringstream choices_s;
        choices_s << "(";
        for (int i = 0; i < choices_vec.size(); i++) {
            choices_s << '"' << choices_vec[i] << "\",";
        }
        std::string choices_str = choices_s.str();
        choices_str.erase(choices_str.length() - 1);
        choices_str += ')';

        send_msg("GETCHOICES " + choices_str + '\n');
    }
}

void ClientHandler::getchoices2_function(std::string arguments)
{
    std::string procedure;

    bool parsed = spirit::parse(arguments.c_str(),
                                '\"' >> 
                                (*(spirit::alnum_p | '-'))
                                 [spirit::assign_a(procedure)]
                                >> '\"',
                                spirit::space_p).full;

    if (!parsed) {
        send_msg("BADCOMMAND\n");
    } else if (!database.procedure_exists(procedure)) {
        send_msg("GETCHOICES BADPROCEDURE\n");
    } else {
        send_choices(procedure);
    }
}

void ClientHandler::getdescription_function(std::string arguments)
{
    std::string procedure;

    bool parsed = spirit::parse(arguments.c_str(),
                                '\"' >> 
                                (*(spirit::alnum_p | '-'))
                                 [spirit::assign_a(procedure)]
                                >> '\"',
                                spirit::space_p).full;

    if (!parsed) {
        send_msg("BADCOMMAND\n");
    } else if (!database.procedure_exists(procedure)) {
        send_msg("GETDESCRIPTION BADPROCEDURE\n");
    } else {
        std::string description = database.get_description(procedure);
        send_msg("GETDESCRIPTION \"" + description + "\"\n");
    }
}

void ClientHandler::getkeyconstants_function(std::string arguments)
{
    std::string procedure;

    bool parsed = spirit::parse(arguments.c_str(),
                                '\"' >> 
                                (*(spirit::alnum_p | '-'))
                                 [spirit::assign_a(procedure)]
                                >> '\"',
                                spirit::space_p).full;

    if (!parsed) {
        send_msg("BADCOMMAND\n");
    } else if (!database.procedure_exists(procedure)) {
        send_msg("GETKEYCONSTANTS BADPROCEDURE\n");
    } else {
        try {
            std::string key = database.get_master_key(procedure).str();
            send_msg("GETKEYCONSTANTS \"" + key + "\"\n");
        } catch (Errors::Empty) {
            send_msg("GETKEYCONSTANTS NOKEY\n");
        }
    }
}

void ClientHandler::getnumchoices_function(std::string arguments)
{
    std::string procedure;

    bool parsed = spirit::parse(arguments.c_str(),
                                '\"' >> 
                                (*(spirit::alnum_p | '-'))
                                 [spirit::assign_a(procedure)]
                                >> '\"',
                                spirit::space_p).full;

    if (!parsed) {
        send_msg("BADCOMMAND\n");
    } else if (!database.procedure_exists(procedure)) {
        send_msg("GETNUMCHOICES BADPROCEDURE\n");
    } else {
        std::stringstream num_choices_ss;
        num_choices_ss << database.get_num_choices(procedure);
        send_msg("GETNUMCHOICES " + num_choices_ss.str() + '\n');
    }
}

void ClientHandler::getnumvotes_function(std::string arguments)
{
    std::string procedure;

    bool parsed = spirit::parse(arguments.c_str(),
                                '\"' >> 
                                (*(spirit::alnum_p | '-'))
                                 [spirit::assign_a(procedure)]
                                >> '\"',
                                spirit::space_p).full;

    if (!parsed) {
        send_msg("BADCOMMAND\n");
    } else if (!database.procedure_exists(procedure)) {
        send_msg("GETNUMVOTES BADPROCEDURE\n");
    } else {
        std::string num_votes = database.get_num_votes(procedure);
        send_msg("GETNUMVOTES " + num_votes + '\n');
    }
}

void ClientHandler::getpubkey_function(std::string arguments)
{
    std::string procedure;

    bool parsed = spirit::parse(arguments.c_str(),
                                '\"' >> 
                                (*(spirit::alnum_p | '-'))
                                 [spirit::assign_a(procedure)]
                                >> '\"',
                                spirit::space_p).full;

    if (!parsed) {
        send_msg("BADCOMMAND\n");
    } else if (!database.procedure_exists(procedure)) {
        send_msg("GETPUBKEY BADPROCEDURE\n");
    } else if (database.get_stage(procedure) < STAGE_VOTING) {
        send_msg("GETPUBKEY BADSTAGE\n");
    } else {
        try {
            std::string pubkey = database.get_pub_key(procedure).str();
            send_msg("GETPUBKEY \"" + pubkey + "\"\n");
        } catch (Errors::Empty) {
            send_msg("GETPUBKEY BADSTAGE\n");
        }
    }
}

void ClientHandler::getresults_function(std::string arguments)
{
    std::string procedure;

    bool parsed = spirit::parse(arguments.c_str(),
                                '\"' >> 
                                (*(spirit::alnum_p | '-'))
                                 [spirit::assign_a(procedure)]
                                >> '\"',
                                spirit::space_p).full;

    if (!parsed) {
        send_msg("BADCOMMAND\n");
    } else if (!database.procedure_exists(procedure)) {
        send_msg("GETRESULTS BADPROCEDURE\n");
    } else if (database.get_stage(procedure) < STAGE_FINISHED) {
        send_msg("GETRESULTS BADSTAGE\n");
    } else {
        std::vector< std::pair<std::string, std::string> > results_vec 
            = database.get_results_str(procedure);

        std::stringstream results_ss;
        
        results_ss << '(';
        for (unsigned int i = 0; i < results_vec.size(); i++) {
            results_ss << "(\"" << results_vec[i].first << "\","
                    << results_vec[i].second << "),";
        }
        std::string results_string(results_ss.str());
        results_string.erase(results_string.length() - 1);
        
        results_string += ')';
        
        send_msg("GETRESULTS " + results_string + '\n');
    }
}

void ClientHandler::getresults2_function(std::string arguments)
{
    std::string procedure;

    bool parsed = spirit::parse(arguments.c_str(),
                                '\"' >> 
                                (*(spirit::alnum_p | '-'))
                                 [spirit::assign_a(procedure)]
                                >> '\"',
                                spirit::space_p).full;

    if (!parsed) {
        send_msg("BADCOMMAND\n");
    } else if (!database.procedure_exists(procedure)) {
        send_msg("GETRESULTS BADPROCEDURE\n");
    } else if (database.get_stage(procedure) < STAGE_FINISHED) {
        send_msg("GETRESULTS BADSTAGE\n");
    } else {
        std::string results = database.get_results_str2(procedure);
        send_msg("BEGIN RESULTS\n" + results + "END RESULTS\n");
    }
}

void ClientHandler::getremaining_function(std::string arguments)
{
    std::string procedure;

    bool parsed = spirit::parse(arguments.c_str(),
                                '\"' >> 
                                (*(spirit::alnum_p | '-'))
                                 [spirit::assign_a(procedure)]
                                >> '\"',
                                spirit::space_p).full;

    if (!parsed) {
        send_msg("BADCOMMAND\n");
    } else if (!database.procedure_exists(procedure)) {
        send_msg("GETREMAINING BADPROCEDURE\n");
    } else {
        std::stringstream remaining;
        remaining << database.get_remaining_authorities(procedure);
        send_msg("GETREMAINING " + remaining.str() + "\n");
    }
}

void ClientHandler::getstage_function(std::string arguments)
{
    std::string procedure;

    bool parsed = spirit::parse(arguments.c_str(),
                                '\"' >> 
                                (*(spirit::alnum_p | '-'))
                                 [spirit::assign_a(procedure)]
                                >> '\"',
                                spirit::space_p).full;

    if (!parsed) {
        send_msg("BADCOMMAND\n");
    } else if (!database.procedure_exists(procedure)) {
        send_msg("GETSTAGE BADPROCEDURE\n");
    } else {
        std::stringstream stage;
        stage << database.get_stage(procedure);
        send_msg("GETSTAGE " + stage.str() + "\n");
    }
}

void ClientHandler::getsum_function(std::string arguments)
{
    std::string procedure;

    bool parsed = spirit::parse(arguments.c_str(),
                                '\"' >> 
                                (*(spirit::alnum_p | '-'))
                                 [spirit::assign_a(procedure)]
                                >> '\"',
                                spirit::space_p).full;

    if (!parsed) {
        send_msg("BADCOMMAND\n");
    } else if (!database.procedure_exists(procedure)) {
        send_msg("GETSUM BADPROCEDURE\n");
    } else if (database.get_stage(procedure) < STAGE_WAITDECRYPT) {
        send_msg("GETSUM BADSTAGE\n");
    } else {
        send_msg("GETSUM \"" + database.get_sum(procedure).str() + "\"\n");
    }
}

void ClientHandler::getthreshold_function(std::string arguments)
{
    std::string procedure;

    bool parsed = spirit::parse(arguments.c_str(),
                                '\"' >> 
                                (*(spirit::alnum_p | '-'))
                                 [spirit::assign_a(procedure)]
                                >> '\"',
                                spirit::space_p).full;

    if (!parsed) {
        send_msg("BADCOMMAND\n");
    } else if (!database.procedure_exists(procedure)) {
        send_msg("GETTHRESHOLD BADPROCEDURE\n");
    } else {
        std::stringstream threshold;
        threshold << database.get_threshold(procedure);
        send_msg("GETTHRESHOLD " + threshold.str() + "\n");
    }
}

void ClientHandler::gettitle_function(std::string arguments)
{
    std::string procedure;

    bool parsed = spirit::parse(arguments.c_str(),
                                '\"' >> 
                                (*(spirit::alnum_p | '-'))
                                 [spirit::assign_a(procedure)]
                                >> '\"',
                                spirit::space_p).full;

    if (!parsed) {
        send_msg("BADCOMMAND\n");
    } else if (!database.procedure_exists(procedure)) {
        send_msg("GETTITLE BADPROCEDURE\n");
    } else {
        std::string title = database.get_procedure_title(procedure);
        send_msg("GETTITLE \"" + title + "\"\n");
    }
}

void ClientHandler::getprivkeylist_function(std::string arguments)
{
    std::string procedure;

    bool parsed = spirit::parse(arguments.c_str(),
                                '\"' >> 
                                (*(spirit::alnum_p | '-'))
                                 [spirit::assign_a(procedure)]
                                >> '\"',
                                spirit::space_p).full;

    if (!parsed) {
        send_msg("BADCOMMAND\n");
    } else if (!database.procedure_exists(procedure)) {
        send_msg("GETPRIVKEYLIST BADPROCEDURE\n");
    } else if (database.get_stage(procedure) < STAGE_WAITGETPRIVKEYS) {
        send_msg("GETPRIVKEYLIST BADSTAGE\n");
    } else {
        try {
            std::vector<adder::ElgamalCiphertext> priv_keys = 
                database.get_priv_key_list(procedure);
            
            std::stringstream key_ss;

            key_ss << '(';
            for (unsigned int i = 0; i < priv_keys.size(); i++) {
                key_ss << "\"" << priv_keys[i].str()
                       << "\",";
            }
            std::string key_string(key_ss.str());
            key_string.erase(key_string.length() - 1);

            key_string += ')';
               
            send_msg("GETPRIVKEYLIST " + key_string + '\n');
        } catch (Errors::Baduser) {
            send_msg("GETPRIVKEYLIST BADUSER\n");
        } catch (Errors::Notauthority) {
            send_msg("GETPRIVKEYLIST NOTAUTHORITY\n");
        } catch (Errors::Badauthstage) {
            send_msg("GETPRIVKEYLIST BADAUTHSTAGE\n");
        }
    }
}

void ClientHandler::getprivkeylist2_function(std::string arguments)
{
    std::string procedure;

    bool parsed = spirit::parse(arguments.c_str(),
                                '\"' >> 
                                (*(spirit::alnum_p | '-'))
                                 [spirit::assign_a(procedure)]
                                >> '\"',
                                spirit::space_p).full;

    if (!parsed) {
        send_msg("BADCOMMAND\n");
    } else if (!database.procedure_exists(procedure)) {
        send_msg("GETPRIVKEYLIST BADPROCEDURE\n");
    } else if (database.get_stage(procedure) < STAGE_WAITGETPRIVKEYS) {
        send_msg("GETPRIVKEYLIST BADSTAGE\n");
    } else {
        send_priv_key_list(procedure);
    }
}

void ClientHandler::getprocedurelist_function(std::string arguments)
{
    bool parsed = spirit::parse(arguments.c_str(), spirit::epsilon_p,
                                spirit::space_p).full;

    if (!parsed) {
        send_msg("BADCOMMAND\n");
    } else {
        send_msg("GETPROCEDURELIST (" + database.get_procedure_list() + ")\n");
    }
}

void ClientHandler::getprocedurelist2_function(std::string arguments)
{
    bool parsed = spirit::parse(arguments.c_str(), spirit::epsilon_p,
                                spirit::space_p).full;

    if (!parsed) {
        send_msg("BADCOMMAND\n");
    } else {
        send_msg("BEGIN PROCEDURELIST\n");
        send_msg(database.get_procedure_list2());
        send_msg("END PROCEDURELIST\n");
    }
}

void ClientHandler::getuserlist_function(std::string arguments)
{
    bool parsed = spirit::parse(arguments.c_str(), spirit::epsilon_p,
                                spirit::space_p).full;

    if (!parsed) {
        send_msg("BADCOMMAND\n");
    } else {
        std::string list_str = database.get_user_list();
        send_msg("GETUSERLIST " +  list_str);
    }
}

void ClientHandler::getuserlist2_function(std::string arguments)
{
    bool parsed = spirit::parse(arguments.c_str(), spirit::epsilon_p,
                                spirit::space_p).full;

    if (!parsed) {
        send_msg("BADCOMMAND\n");
    } else {
        std::string list_str = database.get_user_list2();
        send_msg("BEGIN USERLIST\n" +  list_str + "END USERLIST\n");
    }
}

void ClientHandler::getpubkeylist_function(std::string arguments)
{
    std::string procedure;

    bool parsed = spirit::parse(arguments.c_str(),
                                '\"' >> 
                                (*(spirit::alnum_p | '-'))
                                 [spirit::assign_a(procedure)]
                                >> '\"',
                                spirit::space_p).full;

    if (!parsed) {
        send_msg("BADCOMMAND\n");
    } else if (!database.procedure_exists(procedure)) {
        send_msg("GETPUBKEYLIST BADPROCEDURE\n");
    } else if (database.get_stage(procedure) < STAGE_WAITKEYS) {
        send_msg("GETPUBKEYLIST BADSTAGE\n");
    } else {
        std::string list_str = database.get_pubkey_list(procedure);
        send_msg("BEGIN PUBKEYLIST\n" + list_str + "END PUBKEYLIST\n");
    }
}

void ClientHandler::getpubkeylist2_function(std::string arguments)
{
    std::string procedure;

    bool parsed = spirit::parse(arguments.c_str(),
                                '\"' >> 
                                (*(spirit::alnum_p | '-'))
                                 [spirit::assign_a(procedure)]
                                >> '\"',
                                spirit::space_p).full;

    if (!parsed) {
        send_msg("BADCOMMAND\n");
    } else if (!database.procedure_exists(procedure)) {
        send_msg("GETPUBKEYLIST BADPROCEDURE\n");
    } else if (database.get_stage(procedure) < STAGE_WAITKEYS) {
        send_msg("GETPUBKEYLIST BADSTAGE\n");
    } else {
        std::string list_str = database.get_pubkey_list2(procedure);
        send_msg("BEGIN PUBKEYLIST\n" + list_str + "END PUBKEYLIST\n");
    }
}

void ClientHandler::getvotelist_function(std::string arguments)
{
    std::string procedure;

    bool parsed = spirit::parse(arguments.c_str(),
                                '\"' >> 
                                (*(spirit::alnum_p | '-'))
                                 [spirit::assign_a(procedure)]
                                >> '\"',
                                spirit::space_p).full;

    if (!parsed) {
        send_msg("BADCOMMAND\n");
    } else if (!database.procedure_exists(procedure)) {
        send_msg("GETVOTELIST BADPROCEDURE\n");
    } else if (database.get_stage(procedure) < STAGE_VOTING) {
        send_msg("GETVOTELIST BADSTAGE\n");
    } else {
        std::vector< std::pair<std::string, std::string> > vote_vec 
            = database.get_vote_list(procedure);

        std::stringstream vote_ss;
        
        vote_ss << '(';
        for (unsigned int i = 0; i < vote_vec.size(); i++) {
            vote_ss << "(" << vote_vec[i].first << ","
                    << vote_vec[i].second << "),";
        }
        std::string vote_string(vote_ss.str());
        vote_string.erase(vote_string.length() - 1);
        
        vote_string += ')';
        
        send_msg("GETVOTELIST " + vote_string + '\n');
    }
}

void ClientHandler::getvotelist2_function(std::string arguments)
{
    std::string procedure;

    bool parsed = spirit::parse(arguments.c_str(),
                                '\"' >> 
                                (*(spirit::alnum_p | '-'))
                                 [spirit::assign_a(procedure)]
                                >> '\"',
                                spirit::space_p).full;

    if (!parsed) {
        send_msg("BADCOMMAND\n");
    } else if (!database.procedure_exists(procedure)) {
        send_msg("GETVOTELIST BADPROCEDURE\n");
    } else if (database.get_stage(procedure) < STAGE_VOTING) {
        send_msg("GETVOTELIST BADSTAGE\n");
    } else {
        std::string list_str = database.get_vote_list2(procedure);
        send_msg("BEGIN VOTELIST\n" + list_str + "END VOTELIST\n");
    }
}

void ClientHandler::getauthpubkey_function(std::string arguments)
{
    std::string procedure;
    std::string user_id;

    bool parsed = spirit::parse(arguments.c_str(),
                                '\"' >> 
                                (*(spirit::alnum_p | '-'))
                                 [spirit::assign_a(procedure)]
                                >> '\"'

                                >> '\"' >> 
                                spirit::regex_p("[^\"]+")
                                 [spirit::assign_a(user_id)]
                                >> '\"',

                                spirit::space_p).full;

    if (!parsed) {
        send_msg("BADCOMMAND\n");
    } else if (!database.procedure_exists(procedure)) {
        send_msg("GETAUTHPUBKEY BADPROCEDURE\n");
    } else if (database.get_stage(procedure) < STAGE_WAITKEYS) {
        send_msg("GETAUTHPUBKEY BADSTAGE\n");
    } else {
        try {
            std::string pubkey_str = database.get_auth_pub_key(procedure, 
                                                               user_id).str();
            send_msg("GETAUTHPUBKEY \"" +  pubkey_str + "\"\n");
        } catch (Errors::Empty) {
            send_msg("GETAUTHPUBKEY NOKEY\n");
        }
    }
}

void ClientHandler::getauthstage_function(std::string arguments)
{
    std::string procedure;
    std::string user_id;

    bool parsed = spirit::parse(arguments.c_str(),
                                '\"' >> 
                                (*(spirit::alnum_p | '-'))
                                 [spirit::assign_a(procedure)]
                                >> '\"'

                                >> '\"' >> 
                                spirit::regex_p("[^\"]+")
                                 [spirit::assign_a(user_id)]
                                >> '\"',

                                spirit::space_p).full;

    if (!parsed) {
        send_msg("BADCOMMAND\n");
    } else if (!database.procedure_exists(procedure)) {
        send_msg("GETAUTHSTAGE BADPROCEDURE\n");
    } else {
        try {
            std::stringstream stage_ss;
            stage_ss << database.get_auth_stage(procedure, user_id);

            send_msg("GETAUTHSTAGE " +  stage_ss.str() + '\n');
        } catch (Errors::Empty) {
            send_msg("GETAUTHSTAGE INVALIDAUTHORITY\n");
        }
    }
}

void ClientHandler::getvote_function(std::string arguments)
{
    std::string procedure;
    std::string user_id;

    bool parsed = spirit::parse(arguments.c_str(),
                                '\"' >> 
                                (*(spirit::alnum_p | '-'))
                                 [spirit::assign_a(procedure)]
                                >> '\"'

                                >> '\"' >> 
                                spirit::regex_p("[^\"]+")
                                 [spirit::assign_a(user_id)]
                                >> '\"',

                                spirit::space_p).full;

    if (!parsed) {
        send_msg("BADCOMMAND\n");
    } else if (!database.procedure_exists(procedure)) {
        send_msg("GETVOTE BADPROCEDURE\n");
    } else if (database.get_stage(procedure) < STAGE_VOTING) {
        send_msg("GETVOTE BADSTAGE\n");
    } else {
        try {
            std::string vote_str = database.get_vote(procedure, 
                                                     user_id).str();

            send_msg("GETVOTE \"" + vote_str + "\"\n");
        } catch (Errors::Empty) {
            send_msg("GETVOTE NOVOTE\n");
        }
    }
}

void ClientHandler::getballotproof_function(std::string arguments)
{
    std::string procedure;
    std::string user_id;

    bool parsed = spirit::parse(arguments.c_str(),
                                '\"' >> 
                                (*(spirit::alnum_p | '-'))
                                 [spirit::assign_a(procedure)]
                                >> '\"'

                                >> '\"' >> 
                                spirit::regex_p("[^\"]+")
                                 [spirit::assign_a(user_id)]
                                >> '\"',

                                spirit::space_p).full;

    if (!parsed) {
        send_msg("BADCOMMAND\n");
    } else if (!database.procedure_exists(procedure)) {
        send_msg("GETBALLOTPROOF BADPROCEDURE\n");
    } else if (database.get_stage(procedure) < STAGE_VOTING) {
        send_msg("GETBALLOTPROOF BADSTAGE\n");
    } else {
        try {
            std::string proof_str = database.get_ballot_proof(procedure, 
                                                              user_id).str();

            send_msg("GETBALLOTPROOF \"" + proof_str + "\"\n");
        } catch (Errors::Empty) {
            send_msg("GETBALLOTPROOF NOVOTE\n");
        }
    }
}

void ClientHandler::getshorthash_function(std::string arguments)
{
    std::string procedure;
    std::string user_id;

    bool parsed = spirit::parse(arguments.c_str(),
                                '\"' >> 
                                (*(spirit::alnum_p | '-'))
                                 [spirit::assign_a(procedure)]
                                >> '\"'

                                >> '\"' >> 
                                spirit::regex_p("[^\"]+")
                                 [spirit::assign_a(user_id)]
                                >> '\"',

                                spirit::space_p).full;

    if (!parsed) {
        send_msg("BADCOMMAND\n");
    } else if (!database.procedure_exists(procedure)) {
        send_msg("GETSHORTHASH BADPROCEDURE\n");
    } else if (database.get_stage(procedure) < STAGE_VOTING) {
        send_msg("GETSHORTHASH BADSTAGE\n");
    } else {
        try {
            std::string hash_str = database.get_short_hash(procedure, user_id);

            send_msg("GETSHORTHASH \"" + hash_str + "\"\n");
        } catch (Errors::Empty) {
            send_msg("GETSHORTHASH NOVOTE\n");
        }
    }
}

void ClientHandler::gettimes_function(std::string arguments)
{
    std::string procedure;

    bool parsed = spirit::parse(arguments.c_str(),
                                '\"' >> 
                                (*(spirit::alnum_p | '-'))
                                 [spirit::assign_a(procedure)]
                                >> '\"',
                                spirit::space_p).full;

    if (!parsed) {
        send_msg("BADCOMMAND\n");
    } else if (!database.procedure_exists(procedure)) {
        send_msg("GETTIMES BADPROCEDURE\n");
    } else {
        std::ostringstream times;
        
        times << database.get_create_time(procedure)     << " "
              << database.get_public_key_time(procedure) << " "
              << database.get_polynomial_time(procedure) << " "
              << database.get_secret_key_time(procedure) << " "
              << database.get_vote_time(procedure);
        send_msg("GETTIMES " + times.str() + "\n");
    }
}

void ClientHandler::gettimes2_function(std::string arguments)
{
    std::string procedure;

    bool parsed = spirit::parse(arguments.c_str(),
                                '\"' >> 
                                (*(spirit::alnum_p | '-'))
                                 [spirit::assign_a(procedure)]
                                >> '\"',
                                spirit::space_p).full;

    if (!parsed) {
        send_msg("BADCOMMAND\n");
    } else if (!database.procedure_exists(procedure)) {
        send_msg("GETTIMES BADPROCEDURE\n");
    } else {
        std::ostringstream times;
        
        times << database.get_create_time(procedure)     << " "
              << database.get_public_key_time(procedure) << " "
              << database.get_polynomial_time(procedure) << " "
              << database.get_secret_key_time(procedure) << " "
              << database.get_vote_time(procedure);
        send_msg("GETTIMES " + times.str() + "\n");
    }
}

void ClientHandler::makeuser_function(std::string arguments)
{
    boost::regex e("\\s*\"(.*?)\""
                   "\\s*\"(.*?)\""
                   "\\s*\"(.*?)\""
                   "\\s*\"(.*?)\""
                   "\\s*\"(.*?)\""
                   "\\s*\"(.*?)\"\\s*");
    boost::smatch match;

    bool parsed = boost::regex_match(arguments, match, e);
    
    if (!parsed) {
        send_msg("BADCOMMAND\n");
    } else if (!is_admin) {
        send_msg("MAKEUSER NOTADMIN\n");
    } else {
        
        std::string user_id(match[1].first, match[1].second);
        std::string password(match[2].first, match[2].second);
        std::string first_name(match[3].first, match[3].second);
        std::string middle_name(match[4].first, match[4].second);
        std::string last_name(match[5].first, match[5].second);
        std::string email(match[6].first, match[6].second);

        try {
            database.make_user(user_id, password, first_name, 
                               middle_name, last_name, email);
            send_msg("MAKEUSER OK\n");
        } catch (Errors::Duplicate) {
            send_msg("MAKEUSER USEREXISTS\n");
        }
    }
}

void ClientHandler::progressprocedure_function(std::string arguments)
{
    std::string procedure;

    bool parsed = spirit::parse(arguments.c_str(),
                                '\"' >> 
                                (*(spirit::alnum_p | '-'))
                                 [spirit::assign_a(procedure)]
                                >> '\"',
                                spirit::space_p).full;

    if (!parsed) {
        send_msg("BADCOMMAND\n");
    } else if (!is_admin) {
        send_msg("PROGRESSPROCEDURE NOTADMIN\n");
    } else if (!database.procedure_exists(procedure)) {
        send_msg("PROGRESSPROCEDURE BADPROCEDURE\n");
    } else if (!database.progress_procedure(procedure)) {
        send_msg("PROGRESSPROCEDURE BADSTAGE\n");
    } else {
        send_msg("PROGRESSPROCEDURE OK\n");
    }
}

void ClientHandler::sendpolylist_function(std::string arguments)
{
    using namespace spirit;
    using namespace std;

    string procedure;
    vector< pair<string, string> > poly_vec;
    vector< pair<int, string> > gvalue_vec;

    rule<phrase_scanner_t> expr, str_str, str, int_str,
        int_str_list, str_str_list;

    pair<string, string> strstr_pr;
    pair<int, string> intstr_pr;


    string tmp_str;
    
    str         = (*alnum_p);
    str_str     = ('(' >> ch_p('\"') >> str[assign_a(strstr_pr.first)] >> '\"' >> ','
                   >> '\"' >> str[assign_a(strstr_pr.second)] >> '\"' >> ')')[push_back_a(poly_vec, strstr_pr)];
    int_str     = ('(' >> int_p[assign_a(intstr_pr.first)] >> ','
                   >> '\"' >> str[assign_a(intstr_pr.second)] >> '\"' >> ')') [push_back_a(gvalue_vec, intstr_pr)];
    str_str_list   = str_str % ',';
    int_str_list   = int_str % ',';
    expr           = '(' >> str_str_list >> ')'
                         >> '(' >> int_str_list >> ')'
                         >> '\"' >> (*(alnum_p | ch_p('-')))[assign_a(procedure)]
                         >> '\"';

    bool parsed = parse(arguments.c_str(), expr, space_p).full;

    if (!parsed) {
        send_msg("SENDPOLYLIST BADCOMMAND\n");
    } else if (!database.procedure_exists(procedure)) {
        send_msg("SENDPOLYLIST BADPROCEDURE\n");
    } else if (database.get_stage(procedure) != STAGE_WAITPOLYNOMIAL) {
        send_msg("SENDPOLYLIST BADSTAGE\n");
    } else if (!database.get_is_authority()) {
        send_msg("SENDPOLYLIST BADUSER\n");
    } else {
        try {
            database.add_poly(procedure, poly_vec);
            database.add_gvalue(procedure, gvalue_vec);
            send_msg("SENDPOLYLIST OK\n");
        } catch(Errors::Badauthstage) {
            send_msg("SENDPOLYLIST BADAUTHSTAGE\n");
        }
    }
}

void ClientHandler::sendpublickey_function(std::string arguments)
{
    using namespace spirit;
    using namespace std;

    string pubkey_str;
    string procedure;

    bool parsed = parse(arguments.c_str(), 
                        '\"' >>
                        (*alnum_p)[assign_a(pubkey_str)]
                        >> '\"'

                        >> '\"'
                        >> (*(alnum_p | ch_p('-')))[assign_a(procedure)]
                        >> '\"'
                        , space_p).full;

    if (!parsed) {
        send_msg("SENDPUBLICKEY BADCOMMAND\n");
    } else if (!database.procedure_exists(procedure)) {
        send_msg("SENDPUBLICKEY BADPROCEDURE\n");
    } else if (database.get_stage(procedure) != STAGE_WAITKEYS) {
        send_msg("SENDPUBLICKEY BADSTAGE\n");
    } else if (!database.get_is_authority()) {
        send_msg("SENDPUBLICKEY BADUSER\n");
    } else {
        try {
            ACE_DEBUG((LM_DEBUG, "putting key: %s\n", pubkey_str.c_str()));
            
            adder::PublicKey pub_key;
            pub_key.from_str(pubkey_str);
            
            database.add_key(procedure, pub_key);

            send_msg("SENDPUBLICKEY OK\n");
        } catch (adder::Invalid_key) {
            send_msg("SENDPUBLICKEY BADKEY\n");
        } catch (Errors::Duplicate) {
            send_msg("SENDPUBLICKEY DUPLICATE\n");
        }
    }
}

void ClientHandler::sendsum_function(std::string arguments)
{
    using namespace spirit;
    using namespace std;

    string sum;
    string procedure;

    vector<adder::Integer> sum_vec;
    vector<std::string> sum_str_vec;

    bool parsed = parse(arguments.c_str(),
                        "(" >> (*digit_p)[push_back_a(sum_str_vec)] % ',' >> ")"

                        >> '\"'
                        >> (*(alnum_p | ch_p('-')))[assign_a(procedure)]
                        >> '\"'
                        , space_p).full;
    
    if (!parsed) {
        send_msg("SENDSUM BADCOMMAND\n");
    } else if (!database.procedure_exists(procedure)) {
        send_msg("SENDSUM BADPROCEDURE\n");
    } else if (database.get_stage(procedure) != STAGE_WAITDECRYPT) {
        send_msg("SENDSUM BADSTAGE\n");
    } else if (!database.get_is_authority()) {
        send_msg("SENDSUM BADUSER\n");
    } else {
        try {
            for (unsigned int i = 0; i < sum_str_vec.size(); i++) {
                sum_vec.push_back(adder::Integer(sum_str_vec[i], 10));
            }

            database.add_sum(procedure, sum_vec);

            if (database.get_authority_count(procedure) == 
                database.get_threshold(procedure)) {
                database.decrypt_sum(procedure);
            }

            send_msg("SENDSUM OK\n");
        } catch(Errors::Badauthstage) {
            send_msg("SENDSUM BADAUTHSTAGE\n");
        } catch(Errors::Duplicate) {
            send_msg("SENDSUM DUPLICATE\n");
        }       
    }
}

void ClientHandler::sendvote_function(std::string arguments)
{
    using namespace spirit;
    using namespace std;

    string vote_str;
    string proof_str;
    string procedure;
    
    bool parsed = parse(arguments.c_str(), 
                        '\"' >>
                        (*alnum_p)[assign_a(vote_str)]
                        >> '\"'

                        >> '\"' >>
                        (*alnum_p)[assign_a(proof_str)]
                        >> '\"'

                        >> '\"'
                        >> (*(alnum_p | ch_p('-')))[assign_a(procedure)]
                        >> '\"'
                        , space_p).full;

    if (!parsed) {
        send_msg("SENDVOTE BADCOMMAND\n");
    } else if (!database.procedure_exists(procedure)) {
        send_msg("SENDVOTE BADPROCEDURE\n");
    } else if (database.get_stage(procedure) != STAGE_VOTING) {
        send_msg("SENDVOTE BADSTAGE\n");
    } else if (database.get_user() == "") {
        send_msg("SENDVOTE BADUSER\n");
    } else {
        try {
            adder::PublicKey pub_key = database.get_pub_key(procedure);
            adder::Vote vote;
            adder::VoteProof proof;

            proof.from_str(proof_str);
            vote.from_str(vote_str);
        
            int min_choices = database.get_min_choices(procedure);
            int max_choices = database.get_max_choices(procedure);
            
            Assert<Errors::Invalidproof>
                (proof.verify(vote, pub_key, min_choices, max_choices));
            
            database.add_vote(procedure, vote, proof);

            send_msg("SENDVOTE OK\n");
        } catch (adder::Invalid_vote) {
            send_msg("SENDVOTE BADVOTE\n");
        } catch (adder::Invalid_ciphertext) {
            send_msg("SENDVOTE BADCIPHERTEXT\n");
        } catch (Errors::Invalidproof) {
            send_msg("SENDVOTE INVALIDPROOF\n");
        } catch (Errors::Duplicate) {
            send_msg("SENDVOTE DUPLICATE\n");
        } catch (adder::Invalid_proof) {
            send_msg("SENDVOTE INVALIDPROOF\n");
        }
    }
}

void ClientHandler::session_function(std::string arguments)
{
    std::string session_id;
    std::string procedure;

    bool parsed = spirit::parse(arguments.c_str(),
                                '\"' >> 
                                (*(spirit::alnum_p | '-'))
                                 [spirit::assign_a(session_id)]
                                >> '\"'

                                >> '\"'
                                >> (*(spirit::alnum_p | '-'))
                                    [spirit::assign_a(procedure)]
                                >> '\"',
                                spirit::space_p).full;

    if (!parsed) {
        send_msg("BADCOMMAND\n");
    }
    else if (!database.procedure_exists(procedure)) {
        send_msg("SESSION BADPROCEDURE\n");
    } else {
        try {
            std::string user_id;
            std::string is_authority = "0";
            database.authenticate(session_id, user_id, is_authority, procedure);
            send_msg("SESSION " + is_authority + " \"" + user_id + "\"\n");
        } catch (Errors::Baduser) {
            send_msg("SESSION BADUSER\n");
        } catch (Errors::Badsession) {
            send_msg("SESSION BADSESSION\n");
        }
    }
}

void ClientHandler::startprocedure_function(std::string arguments)
{
    std::string procedure;
    bool parsed = spirit::parse(arguments.c_str(),
                                '\"' >> 
                                (*
                                 (spirit::alnum_p | '-')
                                 )[spirit::assign_a(procedure)] 
                                >> '\"',
                                spirit::space_p).full;

    if (!parsed) {
        send_msg("BADCOMMAND\n");
    } else if (!is_admin) {
        send_msg("STARTPROCEDURE NOTADMIN\n");
    } else if (!database.procedure_exists(procedure)) {
        send_msg("STARTPROCEDURE BADPROCEDURE\n");
    } else if (database.get_stage(procedure) != STAGE_NOTSTARTED) {
        send_msg("STARTPROCEDURE BADSTAGE\n");
    } else {
        database.start_procedure(procedure);
        send_msg("STARTPROCEDURE OK\n");
    }
}

void ClientHandler::stopprocedure_function(std::string arguments)
{
    std::string procedure;
    bool parsed = spirit::parse(arguments.c_str(),
                                '\"' >> 
                                (*
                                 (spirit::alnum_p | '-')
                                 )[spirit::assign_a(procedure)] 
                                >> '\"',
                                spirit::space_p).full;

    if (!parsed) {
        send_msg("BADCOMMAND\n");
    } else if (!is_admin) {
        send_msg("STOPPROCEDURE NOTADMIN\n");
    } else if (!database.procedure_exists(procedure)) {
        send_msg("STOPPROCEDURE BADPROCEDURE\n");
    } else {
        database.set_stage(procedure, STAGE_NOTSTARTED);
        send_msg("STOPPROCEDURE OK\n");
    }
}

void ClientHandler::user_function(std::string arguments)
{
    std::string authority = "0";
    std::string session_id = "";

    std::string user_id;
    std::string password;
    std::string procedure;

    bool parsed = spirit::parse(arguments.c_str(),
                                '\"' >> 
                                spirit::regex_p("[^\"]+")
                                 [spirit::assign_a(user_id)]
                                >> '\"'

                                >> '\"'
                                >> spirit::regex_p("[^\"]+")
                                    [spirit::assign_a(password)]
                                >> '\"'

                                >> '\"'
                                >> (*(spirit::alnum_p | '-'))
                                    [spirit::assign_a(procedure)]
                                >> '\"',
                                spirit::space_p).full;

    if (!parsed) {
        send_msg("BADCOMMAND\n");
    }
    else if (!database.procedure_exists(procedure)) {
        send_msg("USER BADPROCEDURE\n");
    } else {
        try {
            database.authenticate(user_id, password, authority, session_id, procedure);
            send_msg("USER " + authority + " \"" + session_id + "\"\n");
        } catch (Errors::Baduser) {
            send_msg("USER BADUSER\n");
        } catch (Errors::Badstage) {
            send_msg("USER BADSTAGE\n");
        }
    }
}

void ClientHandler::version_function(std::string arguments)
{
    std::string version;
    bool parsed = spirit::parse(arguments.c_str(),
                                '\"' >> 
                                (*
                                 (spirit::alnum_p | spirit::ch_p('.'))
                                 )[spirit::assign_a(version)] 
                                >> '\"',
                                spirit::space_p).full;

    if (!parsed) {
        send_msg("BADCOMMAND\n");
    } else {
        send_msg("VERSION \"1.0\"\n");
    }
}
    
/**
 * Reads a tokenized message and acts according to it.
 * @param tokens the tokenized message.
 */
int ClientHandler::handle(const char* s)
{
    std::string message(s);
    ACE_DEBUG((LM_DEBUG, "handling message:%s", s));

    std::string command;
    std::string arguments;
    spirit::parse(s, (*(spirit::alnum_p))[spirit::assign_a(command)] >> 
                  (*spirit::anychar_p)[spirit::assign_a(arguments)]);

    if (function_map.count(command) == 0) {
        send_msg("BADCOMMAND\n");
    } else {
        (this->*function_map[command])(arguments);
    }

    return 0;
}

/**
 * Processes the data from the client.
 * @param rdbuf the data.
 * @param rdbuf_len the length of the data.
 * @return -1 if there is an error, 0 otherwise.
 */
int ClientHandler::process(char* rdbuf,
                             int rdbuf_len)
{
    char tmpbuf[1];
    ssize_t bytes_read = 0;

    tmpbuf[0] = '\0';
    while (tmpbuf[0] != '\n' && bytes_read < rdbuf_len - 1) {
        if (peer().recv(tmpbuf, 1) > 0) {
            if (tmpbuf[0] != '\r' && tmpbuf[0] != '\n') {
                rdbuf[bytes_read++] = tmpbuf[0];
            }
        } else {
            break;
        }
    }
    switch (bytes_read) {
    case -1:
        ACE_ERROR_RETURN((LM_ERROR,
                          "%p bad read\n",
                          &adder_ctx),
                         -1);
        break;
    case 0:

        ACE_ERROR_RETURN((LM_ERROR,
                          "socket closed unexpectedly (fd = %d)\n",
                          get_handle()),
                         -1);

        break;
    default:
        rdbuf[bytes_read] = 0;

        ACE_DEBUG((LM_DEBUG, "receieved message: %s\n", rdbuf));

        std::string bufbuf(rdbuf);

        if (handle(bufbuf.c_str()) == -1) {
            return -1 ;
        }
    }

    return 0;
}
