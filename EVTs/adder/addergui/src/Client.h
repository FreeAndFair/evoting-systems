/* -*- Mode: C++; tab-width: 4; indent-tabs-mode: nil; c-basic-offset: 4 -*- */

/*  AdderGUI - Graphical client for the Adder system.
    Copyright (C) 2006  The Adder Team

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

#ifndef CLIENT_H
#define CLIENT_H

#include <map>
#include <string>
#include <vector>
#include <utility>

#include <QtNetwork>
#include <QtCrypto>

#include "Procedure.h"
#include "Integer.h"

class Client;
typedef void (Client::* PClient_mem) (const QString);

class Client : public QObject
{
    Q_OBJECT

public:
    enum Error {
        OK, 
        Failure, 
        Login, 
        Baduser, 
        Badstage, 
        Badprocedure, 
        Nokey,
        Novote,
        Duplicate,
        Badkey,
        Badpolylist,
        Badauthstage,
        Notauthority,
        Invalidproof,
        Badproof,
        Badvote
    };

    Client(QObject* parent = 0);
    void send_msg(const QString msg);
    void request_procedure_list();
    void request_version();
    void request_user_list();
    void admin(const QString password);
    void create_procedure(const QString title, const QString text, 
                          const int threshold, const int pubkeytime,
                          const int polytime, const int seckeytime,
                          const int votetime,
                          const int keylength, const int robustness,
                          const int minchoices, const int maxchoices,
                          const std::vector<QString> choices,
                          const std::vector<QString> auths);
    void advance_procedure(const QString proc_id);
    void reset_procedure(const QString proc_id);
    void delete_procedure(const QString proc_id);
    void start_procedure(const QString proc_id);
    void get_choices(const QString proc_id);
    void get_description(const QString proc_id);
    void get_title(const QString proc_id);
    void get_public_key(const QString proc_id);
    void get_key_constants(const QString proc_id);
    void get_num_votes(const QString proc_id);
    void get_num_choices(const QString proc_id);
    void get_cipher_sum(const QString proc_id);
    void get_auth_pubkeys(const QString proc_id);
    void send_public_key(const QString pub_key, const QString proc_id);
    void send_polylist(std::vector< std::pair<QString, QString> > poly_vec,
                       std::vector< std::pair<int, QString> > gvalue_vec,
                       QString proc_id);
    void login(const QString username, const QString password, 
               const QString proc_id);
    void get_private_key_list(const QString proc_id);
    void send_vote(const QString vote, const QString proof, 
                   const QString proc_id);
    void send_sum(std::vector<adder::Integer> sum_vec, 
                  const QString proc_id);
    void get_vote_list(const QString proc_id);
    void get_vote(const QString proc_id, const QString user_id);
    void get_ballot_proof(const QString proc_id, const QString user_id);
    void get_results(const QString proc_id);
    void make_user(const QString username,
                   const QString password,
                   const QString first_name,
                   const QString middle_name,
                   const QString last_name,
                   const QString email);

    void set_using_ssl(bool b) { using_ssl = b; };
    
    bool get_is_admin() const { return is_admin; };
    bool is_connected() const;

signals:
    void error(QAbstractSocket::SocketError);
    void disconnected();
    void connected();
    void hostFound();
    void admin(Client::Error);
    void got_procedure_list(std::vector<Procedure>);
    void got_user_list(std::vector<std::string>);
    void create_procedure(Client::Error);
    void delete_procedure(Client::Error);
    void start_procedure(Client::Error);
    void got_choices(std::vector<QString>);
    void got_description(QString);
    void got_title(Client::Error);
    void logged_in(Client::Error, bool is_authority);
    void got_public_key(Client::Error, QString);
    void got_key_constants(Client::Error, QString);
    void sent_public_key(Client::Error);
    void advance_procedure(Client::Error);
    void reset_procedure(Client::Error);
    void got_auth_pubkeys(Client::Error,
                          std::vector< std::pair<int, std::string> >);
    void sent_polylist(Client::Error);
    void got_private_key_list(Client::Error, std::vector<std::string>);
    void sent_vote(Client::Error);
    void got_num_votes(Client::Error, int);
    void got_cipher_sum(Client::Error, QString);
    void sent_sum(Client::Error);
    void got_vote_list(Client::Error, 
                       std::vector< std::pair<std::string, std::string> >);
    void got_ballot_proof(Client::Error, QString);
    void got_vote(Client::Error, QString);
    void got_num_choices(Client::Error, int);
    void got_results(Client::Error, std::vector< std::pair<std::string, int> >);
    void got_message(const QString &);
    void sending_message(const QString &);
    void make_user(Client::Error);

public slots:
    void connect_to_host(const QString hostname, int port);
    void disconnect();
    void handle_input_sock();
    void handle_input_ssl();
    void sock_readyRead();
    void sock_connected();

    void ssl_handshaken();
    void ssl_readyRead();
    void ssl_readyReadOutgoing();
    void ssl_closed();
    void ssl_error();

private:
    QTcpSocket* socket;
    QCA::TLS* ssl;

    bool using_ssl;

    QString host;
    int port;

    QBuffer buffer;
    QByteArray byte_array;

    bool is_admin;

    void initialize_function_map();

    void admin_handler(const QString arguments);
    void createprocedure_handler(const QString arguments);
    void deleteprocedure_handler(const QString arguments);
    void getauthpubkeys_handler(const QString arguments);
    void getballotproof_handler(const QString arguments);
    void getchoices_handler(const QString arguments);
    void getdescription_handler(const QString arguments);
    void getkeyconstants_handler(const QString arguments);
    void getnumvotes_handler(const QString arguments);
    void getnumchoices_handler(const QString arguments);
    void getsum_handler(const QString arguments);
    void getprivkeylist_handler(const QString arguments);
    void getprocedurelist_handler(const QString arguments);
    void getpubkey_handler(const QString arguments);
    void getresults_handler(const QString arguments);
    void gettitle_handler(const QString arguments);
    void getvote_handler(const QString arguments);
    void getvotelist_handler(const QString arguments);
    void getuserlist_handler(const QString arguments);
    void makeuser_handler(const QString arguments);
    void progressprocedure_handler(const QString arguments);
    void version_handler(const QString arguments);
    void sendpublickey_handler(const QString arguments);
    void sendpolylist_handler(const QString arguments);
    void sendsum_handler(const QString arguments);
    void sendvote_handler(const QString arguments);
    void startprocedure_handler(const QString arguments);
    void stopprocedure_handler(const QString arguments);
    void user_handler(const QString arguments);

    static std::map<std::string, PClient_mem> function_map;
};

#endif // CLIENT_H
