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
 * @file ClientHandler.hh
 * Interface of the ClientHandler class.
 */

#ifndef CLIENTHANDLER_HH
#define CLIENTHANDLER_HH

#include <string>
#include <vector>
#include <sstream>
#include <map>

#include "ace/Svc_Handler.h"
#ifdef ENABLE_SSL
#include "ace/SSL/SSL_SOCK_Stream.h"
#else
#include "ace/SOCK_Stream.h"
#endif
#include "ace/Time_Value.h"

#include "libadder.h"
#include "Polynomial.h"

#include "Database.hh"
#include "Utilities.hh"

#ifdef ENABLE_SSL
#define ADDERD_CERT "adderd-cert.pem"
#define ADDERD_KEY  "adderd-key.pem"
#endif

enum KEY_CODE { KEY_SUCCESS, KEY_FAILURE, KEY_DUPLICATE, KEY_INVALID };
enum VOTE_CODE { VOTE_SUCCESS, VOTE_FAILURE, VOTE_DUPLICATE, VOTE_INVALID };
enum SUM_CODE { SUM_SUCCESS, SUM_FAILURE, SUM_DUPLICATE, SUM_INVALID };
enum POLY_CODE { POLY_SUCCESS, POLY_FAILURE, POLY_DUPLICATE, POLY_INVALID };
enum PROC_CODE { PROC_SUCCESS, PROC_FAILURE, PROC_DUPLICATE, PROC_INVALID };
enum GVALUE_CODE { GVALUE_SUCCESS, GVALUE_FAILURE, GVALUE_DUPLICATE, GVALUE_INVALID };

class ClientHandler;
typedef void (ClientHandler::* PClientHandler_mem) (std::string);

/**
 * Class to represent the service handler for the client.
 */
#ifdef ENABLE_SSL
class ClientHandler : public ACE_Svc_Handler<ACE_SSL_SOCK_STREAM, ACE_NULL_SYNCH>
#else
class ClientHandler : public ACE_Svc_Handler<ACE_SOCK_STREAM, ACE_NULL_SYNCH>
#endif
{
public:
    ClientHandler();
    ~ClientHandler();

    void destroy();
    int open(void* acceptor);
    int close(u_long flags = 0);

    virtual int handle_close(ACE_HANDLE handle = ACE_INVALID_HANDLE,
                             ACE_Reactor_Mask mask = ACE_Event_Handler::ALL_EVENTS_MASK);

    static void initialize_function_map();

protected:
    int svc();
    KEY_CODE put_key();
    VOTE_CODE put_vote();
    SUM_CODE put_sum();
    void process_createprocedure(std::vector<std::string> tokens);
    void process_pubkey(std::vector<std::string> tokens);
    void process_sum(std::vector<std::string> tokens);
    void process_vote(std::vector<std::string> tokens);
    int process_poly(std::vector<std::string> tokens);
    int process_gvalue(std::vector<std::string> tokens);
    int handle_message(std::vector<std::string> tokens);
    int handle(const char* s);
    int process(char* rdbuf, int rdbuf_len);
    void send_msg(std::string message);
    void send_priv_key(std::string proc_id);
    void send_priv_key_list(std::string proc_id);
    void send_auth_pub_keys(std::string proc_id);
    void send_choices(std::string proc_id);

    /* Command functions. */
    void admin_function(std::string arguments);
    void createprocedure_function(std::string arguments);
    void deleteprocedure_function(std::string arguments);
    void getauthpubkey_function(std::string arguments);
    void getauthpubkeys_function(std::string arguments);
    void getauthstage_function(std::string arguments);
    void getballotproof_function(std::string arguments);
    void getbase_function(std::string arguments);
    void getchoices_function(std::string arguments);
    void getdescription_function(std::string arguments);
    void getkeyconstants_function(std::string arguments);
    void getnumchoices_function(std::string arguments);
    void getnumvotes_function(std::string arguments);
    void getprivkeylist_function(std::string arguments);
    void getprocedurelist_function(std::string arguments);
    void getpubkey_function(std::string arguments);
    void getpubkeylist_function(std::string arguments);
    void getremaining_function(std::string arguments);
    void getresults_function(std::string arguments);
    void getshorthash_function(std::string arguments);
    void getstage_function(std::string arguments);
    void getsum_function(std::string arguments);
    void getthreshold_function(std::string arguments);
    void gettimes_function(std::string arguments);
    void gettitle_function(std::string arguments);
    void getuserlist_function(std::string arguments);
    void getvote_function(std::string arguments);
    void getvotelist_function(std::string arguments);
    void makeuser_function(std::string arguments);
    void progressprocedure_function(std::string arguments);
    void sendpolylist_function(std::string arguments);
    void sendpublickey_function(std::string arguments);
    void sendsum_function(std::string arguments);
    void sendvote_function(std::string arguments);
    void session_function(std::string arguments);
    void startprocedure_function(std::string arguments);
    void stopprocedure_function(std::string arguments);
    void user_function(std::string arguments);
    void version_function(std::string arguments);

    void getauthpubkeys2_function(std::string arguments);
    void getchoices2_function(std::string arguments);
    void getprivkeylist2_function(std::string arguments);
    void getprocedurelist2_function(std::string arguments);
    void getpubkeylist2_function(std::string arguments);
    void getresults2_function(std::string arguments);
    void gettimes2_function(std::string arguments);
    void getuserlist2_function(std::string arguments);
    void getvotelist2_function(std::string arguments);

    Database database; /**< Object to represent the database. */

    bool getting_vote; /**< Whether the server is currently receiving a vote. */
    bool getting_key; /**< Whether the server is currently receiving a key. */
    bool getting_sum; /**< Whether the server is currently receiving a sum. */
    bool getting_polylist; /**< Whether the server is currently receiving a polynomial list. */
    bool getting_gvaluelist; /**< Whether the server is currently receiving a g-value list. */
    bool getting_createprocedure; /**< Whether the server is currently receiving new procedure info. */

    std::stringstream buffer; /**< Buffer. */

    adder::Context adder_ctx; /**< The context for libadder
                                 functions. */

    bool is_admin;

    static std::map<std::string, PClientHandler_mem> function_map;
};

#endif /* CLIENTHANDLER_HH */
