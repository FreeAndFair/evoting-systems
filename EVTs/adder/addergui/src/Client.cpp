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

#include <QtGui>
#include <QtNetwork>
#include <QtCrypto>

#include <iostream>
#include <string>
#include <map>
#include <algorithm>

#include <boost/spirit/core.hpp>
#include <boost/spirit/utility/regex.hpp>

#include "Procedure.h"
#include "Client.h"

using namespace std;
using namespace boost::spirit;

map<string, PClient_mem> Client::function_map;

void showCertInfo(const QCA::Certificate &cert)
{
	printf("-- Cert --\n");
	printf(" CN: %s\n", qPrintable(cert.commonName()));
	printf(" Valid from: %s, until %s\n",
		qPrintable(cert.notValidBefore().toString()),
		qPrintable(cert.notValidAfter().toString()));
	printf(" PEM:\n%s\n", qPrintable(cert.toPEM()));
}

static QString validityToString(QCA::Validity v)
{
	QString s;
	switch(v)
	{
		case QCA::ValidityGood:
			s = "Validated";
			break;
		case QCA::ErrorRejected:
			s = "Root CA is marked to reject the specified purpose";
			break;
		case QCA::ErrorUntrusted:
			s = "Certificate not trusted for the required purpose";
			break;
		case QCA::ErrorSignatureFailed:
			s = "Invalid signature";
			break;
		case QCA::ErrorInvalidCA:
			s = "Invalid CA certificate";
			break;
		case QCA::ErrorInvalidPurpose:
			s = "Invalid certificate purpose";
			break;
		case QCA::ErrorSelfSigned:
			s = "Certificate is self-signed";
			break;
		case QCA::ErrorRevoked:
			s = "Certificate has been revoked";
			break;
		case QCA::ErrorPathLengthExceeded:
			s = "Maximum certificate chain length exceeded";
			break;
		case QCA::ErrorExpired:
			s = "Certificate has expired";
			break;
		case QCA::ErrorExpiredCA:
			s = "CA has expired";
			break;
		case QCA::ErrorValidityUnknown:
		default:
			s = "General certificate validation error";
			break;
	}
	return s;
}

Client::Client(QObject* parent)
    :QObject(parent), using_ssl(true), is_admin(false)
{
    initialize_function_map();

    socket = new QTcpSocket(this);

    connect(socket, SIGNAL(error(QAbstractSocket::SocketError)),
            this, SIGNAL(error(QAbstractSocket::SocketError)));

    connect(socket, SIGNAL(disconnected()), this, SIGNAL(disconnected()));
    connect(socket, SIGNAL(connected()), this, SLOT(sock_connected()));
    connect(socket, SIGNAL(readyRead()), this, SLOT(sock_readyRead()));
    connect(socket, SIGNAL(hostFound()), this, SIGNAL(hostFound()));

    ssl = new QCA::TLS(0);
    connect(ssl, SIGNAL(handshaken()), this, SLOT(ssl_handshaken()));
    connect(ssl, SIGNAL(readyRead()), this, SLOT(ssl_readyRead()));
    connect(ssl, SIGNAL(readyReadOutgoing()),
            this, SLOT(ssl_readyReadOutgoing()));
    connect(ssl, SIGNAL(closed()), this, SLOT(ssl_closed()));
    connect(ssl, SIGNAL(error()), this, SLOT(ssl_error()));

    //    connect(&buffer, SIGNAL(readyRead()), this, SLOT(handle_input_ssl()));

    buffer.open(QBuffer::ReadWrite);
}

void Client::initialize_function_map()
{
    function_map["ADMIN"] = &Client::admin_handler;
    function_map["CREATEPROCEDURE"] = &Client::createprocedure_handler;
    function_map["DELETEPROCEDURE"] = &Client::deleteprocedure_handler;
    function_map["GETAUTHPUBKEYS"] = &Client::getauthpubkeys_handler;
    function_map["GETBALLOTPROOF"] = &Client::getballotproof_handler;
    function_map["GETCHOICES"] = &Client::getchoices_handler;
    function_map["GETDESCRIPTION"] = &Client::getdescription_handler;
    function_map["GETKEYCONSTANTS"] = &Client::getkeyconstants_handler;
    function_map["GETNUMCHOICES"] = &Client::getnumchoices_handler;
    function_map["GETNUMVOTES"] = &Client::getnumvotes_handler;
    function_map["GETPRIVKEYLIST"] = &Client::getprivkeylist_handler;
    function_map["GETPROCEDURELIST"] = &Client::getprocedurelist_handler;
    function_map["GETPUBKEY"] = &Client::getpubkey_handler;
    function_map["GETRESULTS"] = &Client::getresults_handler;
    function_map["GETSUM"] = &Client::getsum_handler;
    function_map["GETTITLE"] = &Client::gettitle_handler;
    function_map["GETUSERLIST"] = &Client::getuserlist_handler;
    function_map["GETVOTE"] = &Client::getvote_handler;
    function_map["GETVOTELIST"] = &Client::getvotelist_handler;
    function_map["MAKEUSER"] = &Client::makeuser_handler;
    function_map["PROGRESSPROCEDURE"] = &Client::progressprocedure_handler;
    function_map["SENDPUBLICKEY"] = &Client::sendpublickey_handler;
    function_map["SENDPOLYLIST"] = &Client::sendpolylist_handler;
    function_map["SENDSUM"] = &Client::sendsum_handler;
    function_map["SENDVOTE"] = &Client::sendvote_handler;
    function_map["STARTPROCEDURE"] = &Client::startprocedure_handler;
    function_map["STOPPROCEDURE"] = &Client::stopprocedure_handler;
    function_map["USER"] = &Client::user_handler;
    function_map["VERSION"] = &Client::version_handler;
}

void Client::sock_connected()
{
    if (!using_ssl) {
        cout << "Connected!\n";
        emit connected();
    } else {
        QCA::CertificateCollection rootCerts = QCA::systemStore();
        
        QSettings settings;
        QString cert_string = settings.value("ssl/certificate", "").toString();
        rootCerts.addCertificate(QCA::Certificate::fromPEM(cert_string));

        if (!QCA::haveSystemStore()) {
            cout << "Warning: no root certs\n";
        } else {
            ssl->setTrustedCertificates(rootCerts);
        }

        ssl->startClient(host);
    }
}

void Client::connect_to_host(const QString hostname, int port)
{
    is_admin = false;
    host = hostname;
    this->port = port;

    socket->connectToHost(hostname, port);
}

void Client::ssl_handshaken()
{
    QCA::TLS::IdentityResult r = ssl->peerIdentityResult();

    printf("Successful SSL handshake using %s (%i of %i bits)\n",
           qPrintable(ssl->cipherSuite()),
           ssl->cipherBits(),
           ssl->cipherMaxBits());

    if(r != QCA::TLS::NoCertificate) {
			QCA::Certificate cert = ssl->peerCertificateChain().primary();
			if(!cert.isNull())
				showCertInfo(cert);
    }
    
    QString str = "Peer Identity: ";
    if(r == QCA::TLS::Valid)
        str += "Valid";
    else if(r == QCA::TLS::HostMismatch)
        str += "Error: Wrong certificate";
    else if(r == QCA::TLS::InvalidCertificate)
        str += "Error: Invalid certificate.\n -> Reason: " +
            validityToString(ssl->peerCertificateValidity());
    else
        str += "Error: No certificate";
    printf("%s\n", qPrintable(str));    

    emit connected();
}

void Client::ssl_readyRead()
{
    QByteArray a = ssl->read();
    buffer.write(a);
    handle_input_ssl();
}

void Client::ssl_readyReadOutgoing()
{
    int num = -1;

    while (num != 0) {
        QByteArray outgoing = ssl->readOutgoing(&num);
        socket->write(outgoing);
    }
}

void Client::ssl_closed()
{
}

void Client::ssl_error()
{
}

void Client::disconnect()
{
    socket->close();
}

void Client::send_msg(const QString msg)
{
    QString s(msg);
    if (using_ssl) {
        ssl->write((s + '\n').toLatin1());
    } else {
        socket->write((s + '\n').toStdString().c_str(), s.length() + 1);
    }
    
    emit sending_message(msg);
}

void Client::sock_readyRead()
{
    if (using_ssl) {
        ssl->writeIncoming(socket->readAll());
    } else {
        handle_input_sock();
    }
}

void Client::handle_input_sock()
{
    char line[1024 * 100]; // FIXME: Don't use a magic number here.

    while (socket->canReadLine()) {
        socket->readLine(line, sizeof(line));

        string command;
        string arguments;

        emit got_message(line);

        parse(line, (*alpha_p)[assign_a(command)] >>
              (*anychar_p)[assign_a(arguments)]);

        if (function_map.count(command)) {
            (this->*function_map[command])(QString(arguments.c_str()).simplified());
        } else {
            //            cerr << "Received unknown command: " << command << endl;
        }
    }
}

void Client::handle_input_ssl()
{
    char line[1024 * 100]; // FIXME: Don't use a magic number here.

    buffer.seek(0);

    while (buffer.canReadLine()) {
        int bytes = buffer.readLine(line, sizeof(line));
        buffer.seek(0);
        buffer.buffer().remove(0, bytes);
		buffer.seek(0);
        string command;
        string arguments;

        emit got_message(line);

        parse(line, (*alpha_p)[assign_a(command)] >>
              (*anychar_p)[assign_a(arguments)]);

        if (function_map.count(command)) {
            (this->*function_map[command])(QString(arguments.c_str()).simplified());
        } else {
            //            cerr << "Received unknown command: " << command << endl;
        }
    }
}

void Client::version_handler(const QString arguments)
{
    QRegExp rx("\\s*\"1.0\"\\s*");

    if (!rx.exactMatch(arguments)) {
        cerr << "Bad server version: " << arguments.toStdString() << "\n";
        disconnect();
    }
}

void Client::admin_handler(const QString arguments)
{
    if (arguments == QString("OK")) {
        is_admin = true;
        emit admin(Client::OK);
    } else {
        is_admin = false;
        emit admin(Client::Baduser);
    }
}

void Client::createprocedure_handler(const QString arguments)
{
    if (arguments == QString("OK")) {
        emit create_procedure(Client::OK);
    } else {
        emit create_procedure(Client::Failure);
    }
}

void Client::deleteprocedure_handler(const QString arguments)
{
    if (arguments == QString("OK")) {
        emit delete_procedure(Client::OK);
    } else {
        emit delete_procedure(Client::Failure);
    }
}

void Client::getauthpubkeys_handler(const QString arguments)
{
    if (arguments == QString("BADPROCEDURE")) {
        emit got_auth_pubkeys(Client::Badprocedure,
                              vector< pair<int, string> >());
    } else if (arguments == QString("BADSTAGE")) {
        emit got_auth_pubkeys(Client::Badstage,
                              vector< pair<int, string> >());
    } else {
        rule<phrase_scanner_t> auth_key_pair, expr;
        pair<int, string> tmp_pair;
        vector< pair<int, string> > pair_vec;
        
        auth_key_pair = 
            '(' >> int_p[assign_a(tmp_pair.first)]
                >> ','
                >> (*alnum_p)[assign_a(tmp_pair.second)]
                >> ')';
        expr = '(' >> auth_key_pair[push_back_a(pair_vec, tmp_pair)] % ',' 
                   >> ')';

        bool parsed = parse(arguments.simplified().toStdString().c_str(),
                             expr, space_p).full;

        if (!parsed) {
            cerr << "could not parse\n";
        } else {
            emit got_auth_pubkeys(Client::OK, pair_vec);
        }
    }
}

void Client::getballotproof_handler(const QString arguments)
{
    if (arguments == QString("BADPROCEDURE")) {
        emit got_ballot_proof(Client::Badprocedure, QString());
    } else if (arguments == QString("INVALIDUSER")) {
        emit got_ballot_proof(Client::Baduser, QString());
    } else if (arguments == QString("BADSTAGE")) {
        emit got_ballot_proof(Client::Badstage, QString());
    } else if (arguments == QString("NOVOTE")) {
        emit got_ballot_proof(Client::Novote, QString());
    } else {
        QRegExp rx("^\\s*\"(.*)\"\\s*$");
        rx.setMinimal(true);
        rx.exactMatch(arguments);
        QString ballot_proof = rx.capturedTexts().at(1);
        emit got_ballot_proof(Client::OK, ballot_proof);
    }
}

void Client::getchoices_handler(const QString arguments)
{
    std::vector<std::string> choices_vec;

    rule<phrase_scanner_t> expr;
    expr = '(' 
        >> 
        (ch_p('\"') >> regex_p("[^\"]+")[push_back_a(choices_vec)] >> '\"') 
        % ',' >> ch_p(')');
    bool parsed = parse(arguments.simplified().toStdString().c_str(),
                        expr, space_p).full;

    if (!parsed) {
        cerr << "could not parse\n";
    } else {
        std::vector<QString> qchoices_vec;
        for (unsigned int i = 0; i < choices_vec.size(); i++) {
            qchoices_vec.push_back(QString(choices_vec[i].c_str()));
        }
        emit got_choices(qchoices_vec);
    }
}

void Client::getdescription_handler(const QString arguments)
{
    if (arguments != QString("BADPROCEDURE")) {
        QRegExp rx("^\\s*\"(.*)\"\\s*$");
        rx.setMinimal(true);
        rx.exactMatch(arguments);
        QString description = rx.capturedTexts().at(1);
        emit got_description(description);
    }
}

void Client::getkeyconstants_handler(const QString arguments)
{
    if (arguments == QString("BADPROCEDURE")) {
        emit got_public_key(Client::Badprocedure, QString());
    } else if (arguments == QString("NOKEY")) {
        emit got_public_key(Client::Nokey, QString());
    } else {
        QRegExp rx("^\\s*\"(.*)\"\\s*$");
        rx.setMinimal(true);
        rx.exactMatch(arguments);
        QString key_constants = rx.capturedTexts().at(1);
        emit got_key_constants(Client::OK, key_constants);
    }
}

void Client::getnumchoices_handler(const QString arguments)
{
    if (arguments == QString("BADPROCEDURE")) {
        emit got_num_choices(Client::Badprocedure, 0);
    } else {
        QRegExp rx("^\\s*(\\d*)\\s*$");
        rx.setMinimal(true);
        rx.exactMatch(arguments);
        int num_choices = rx.capturedTexts().at(1).toInt();
        emit got_num_choices(Client::OK, num_choices);
    }
}

void Client::getnumvotes_handler(const QString arguments)
{
    if (arguments == QString("BADPROCEDURE")) {
        emit got_num_votes(Client::Badprocedure, 0);
    } else {
        QRegExp rx("^\\s*(\\d*)\\s*$");
        rx.setMinimal(true);
        rx.exactMatch(arguments);
        int num_votes = rx.capturedTexts().at(1).toInt();
        emit got_num_votes(Client::OK, num_votes);
    }
}

void Client::getprocedurelist_handler(const QString arguments)
{
    std::vector<Procedure> procedure_vec;

    std::string tmp_id;
    std::string tmp_title;

    vector<string> id_vec;
    vector<string> title_vec;
    vector<int> stage_vec;
    vector<int> remaining_vec;
    vector<int> threshold_vec;
    vector<int> robustness_vec;
    vector<int> minchoices_vec;
    vector<int> maxchoices_vec;

    rule<phrase_scanner_t> proc_expr, expr;

    Procedure tmp_proc;
    
    proc_expr = (ch_p('(') >> 
                 '\"' >> (*(alnum_p | '-'))[push_back_a(id_vec)] >> '\"' >> ch_p(',') >>
                 '\"' >> (regex_p("[^\"]*"))[push_back_a(title_vec)] >> '\"' >> ch_p(',') >> 
                 int_p[push_back_a(stage_vec)] >> ch_p(',')
                 >> int_p[push_back_a(remaining_vec)] >> ch_p(',')
                 >> int_p[push_back_a(threshold_vec)] >> ch_p(',')
                 >> int_p[push_back_a(robustness_vec)] >> ch_p(',')
                 >> int_p[push_back_a(minchoices_vec)] >> ch_p(',')
                 >> int_p[push_back_a(maxchoices_vec)]
                 >> ch_p(')'));

    expr = '(' >> *(proc_expr
        % ',') >> ')';

    bool parsed = parse(arguments.simplified().toStdString().c_str(),
                        expr, space_p).full;

    if (!parsed) {
        cerr << "could not parse\n";
    } else {
        for (unsigned int i = 0; i < id_vec.size(); i++) {
            procedure_vec.push_back(Procedure(id_vec[i], title_vec[i], 
                                              (Procedure::STAGE)stage_vec[i],
                                              remaining_vec[i],
                                              threshold_vec[i], 
                                              robustness_vec[i],
                                              minchoices_vec[i],
                                              maxchoices_vec[i]));
        }

        emit got_procedure_list(procedure_vec);
    }
}

void Client::getpubkey_handler(const QString arguments)
{
    if (arguments == QString("BADPROCEDURE")) {
        emit got_public_key(Client::Badprocedure, QString());
    } else if (arguments == QString("BADSTAGE")) {
        emit got_public_key(Client::Badstage, QString());
    } else {
        QRegExp rx("^\\s*\"(.*)\"\\s*$");
        rx.setMinimal(true);
        rx.exactMatch(arguments);
        QString pub_key = rx.capturedTexts().at(1);
        emit got_public_key(Client::OK, pub_key);
    }
}

void Client::getprivkeylist_handler(const QString arguments)
{
    if (arguments == QString("BADPROCEDURE")) {
        emit got_private_key_list(Client::Badprocedure,
                               std::vector<std::string>());
    } else if (arguments == QString("BADSTAGE")) {
        emit got_private_key_list(Client::Badstage,
                               std::vector<std::string>());
    } else if (arguments == QString("BADUSER")) {
        emit got_private_key_list(Client::Baduser,
                               std::vector<std::string>());
    } else if (arguments == QString("NOTAUTHORITY")) {
        emit got_private_key_list(Client::Notauthority,
                               std::vector<std::string>());
    } else if (arguments == QString("BADAUTHSTAGE")) {
        emit got_private_key_list(Client::Badauthstage,
                               std::vector<std::string>());
    } else {
        std::vector<std::string> key_vec;
        
        rule<phrase_scanner_t> expr;
        expr = '(' >> (ch_p('\"') >> (*alnum_p)[push_back_a(key_vec)] >> '\"') % ',' >> ch_p(')');
        bool parsed = parse(arguments.simplified().toStdString().c_str(),
                            expr, space_p).full;
        
        if (!parsed) {
            cerr << "could not parse\n";
        } else {
            emit got_private_key_list(Client::OK,
                                   key_vec);
        }
    }
}

void Client::getresults_handler(const QString arguments)
{
    if (arguments == QString("BADPROCEDURE")) {
        emit got_results(Client::Badprocedure,
                         vector< pair<string, int> >());
    } else if (arguments == QString("BADSTAGE")) {
        emit got_results(Client::Badstage,
                         vector< pair<string, int> >());
    } else {
        rule<phrase_scanner_t> results_pair, expr;
        pair<string, int> tmp_pair;
        vector< pair<string, int> > pair_vec;
        
        results_pair = 
            '(' >> ch_p("\"") >> regex_p("[^\"]+")[assign_a(tmp_pair.first)]
                >> ch_p("\"") >> ','
                >> int_p[assign_a(tmp_pair.second)]
                >> ')';
        expr = '(' >> results_pair[push_back_a(pair_vec, tmp_pair)] % ',' 
                   >> ')';

        bool parsed = parse(arguments.simplified().toStdString().c_str(),
                             expr, space_p).full;

        if (!parsed) {
            cerr << "could not parse\n";
        } else {
            emit got_results(Client::OK, pair_vec);
        }
    }
}

void Client::getsum_handler(const QString arguments)
{
    if (arguments == QString("BADPROCEDURE")) {
        emit got_cipher_sum(Client::Badprocedure, QString());
    } else if (arguments == QString("BADSTAGE")) {
        emit got_cipher_sum(Client::Badstage, QString());
    } else {
        QRegExp rx("^\\s*\"(.*)\"\\s*$");
        rx.setMinimal(true);
        rx.exactMatch(arguments);
        QString sum = rx.capturedTexts().at(1);
        emit got_cipher_sum(Client::OK, sum);
    }
}

void Client::gettitle_handler(const QString arguments)
{
    if (arguments == QString("OK")) {
        emit got_title(Client::OK);
    } else {
        emit got_title(Client::Failure);
    }
}

void Client::getuserlist_handler(const QString arguments)
{
    std::vector<std::string> user_vec;

    rule<phrase_scanner_t> expr;
    expr = '(' >> (ch_p('\"') >> regex_p("[^\"]+")[push_back_a(user_vec)] >> '\"') % ',' >> ch_p(')');
    bool parsed = parse(arguments.simplified().toStdString().c_str(),
                        expr, space_p).full;

    if (!parsed) {
        cerr << "could not parse\n";
    } else {
        sort(user_vec.begin(), user_vec.end());
        emit got_user_list(user_vec);
    }
}

void Client::getvotelist_handler(const QString arguments)
{
    if (arguments == QString("BADPROCEDURE")) {
        emit got_vote_list(Client::Badprocedure,
                           vector< pair<string, string> >());
    } else if (arguments == QString("BADSTAGE")) {
        emit got_vote_list(Client::Badstage,
                           vector< pair<string, string> >());
    } else {
        rule<phrase_scanner_t> vote_pair, expr;
        pair<string, string> tmp_pair;
        vector< pair<string, string> > pair_vec;
        
        vote_pair = 
            '(' >> ch_p("\"") >> regex_p("[^\"]+")[assign_a(tmp_pair.first)]
                >> ch_p("\"") >> ',' >> ch_p("\"")
                >> (*(alnum_p | ch_p('-') | ch_p(':')))[assign_a(tmp_pair.second)]
                >> ch_p("\"") >> ')';
        expr = '(' >> vote_pair[push_back_a(pair_vec, tmp_pair)] % ',' 
                   >> ')';

        bool parsed = parse(arguments.simplified().toStdString().c_str(),
                             expr, space_p).full;

        if (!parsed) {
            cerr << "could not parse\n";
        } else {
            emit got_vote_list(Client::OK, pair_vec);
        }
    }
}

void Client::getvote_handler(const QString arguments)
{
    if (arguments == QString("BADPROCEDURE")) {
        emit got_vote(Client::Badprocedure, QString());
    } else if (arguments == QString("INVALIDUSER")) {
        emit got_vote(Client::Baduser, QString());
    } else if (arguments == QString("BADSTAGE")) {
        emit got_vote(Client::Badstage, QString());
    } else if (arguments == QString("NOVOTE")) {
        emit got_vote(Client::Novote, QString());

    } else {
        QRegExp rx("^\\s*\"(.*)\"\\s*$");
        rx.setMinimal(true);
        rx.exactMatch(arguments);
        QString vote = rx.capturedTexts().at(1);
        emit got_vote(Client::OK, vote);
    }
}

void Client::makeuser_handler(const QString arguments)
{
    if (arguments == QString("USEREXISTS")) {
        emit make_user(Client::Duplicate);
    } else {
        emit make_user(Client::OK);
    }
}

void Client::progressprocedure_handler(const QString arguments)
{
    if (arguments == QString("BADPROCEDURE")) {
        emit advance_procedure(Client::Badprocedure);
    } else if (arguments == QString("BADSTAGE")) {
        emit advance_procedure(Client::Badstage);
    } else {
        emit advance_procedure(Client::OK);
    }
}

void Client::sendpublickey_handler(const QString arguments)
{
    if (arguments == QString("BADPROCEDURE")) {
        emit sent_public_key(Client::Badprocedure);
    } else if (arguments == QString("BADUSER")) {
        emit sent_public_key(Client::Baduser);
    } else if (arguments == QString("BADSTAGE")) {
        emit sent_public_key(Client::Badstage);
    } else if (arguments == QString("DUPLICATE")) {
        emit sent_public_key(Client::Duplicate);
    } else if (arguments == QString("BADKEY")) {
        emit sent_public_key(Client::Badkey);
    } else {
        emit sent_public_key(Client::OK);
    }
}

void Client::sendpolylist_handler(const QString arguments)
{
    if (arguments == QString("BADPROCEDURE")) {
        emit sent_polylist(Client::Badprocedure);
    } else if (arguments == QString("BADSTAGE")) {
        emit sent_polylist(Client::Badstage);
    } else if (arguments == QString("BADPOLYLIST")) {
        emit sent_polylist(Client::Badpolylist);
    } else if (arguments == QString("BADUSER")) {
        emit sent_polylist(Client::Baduser);
    } else if (arguments == QString("BADAUTHSTAGE")) {
        emit sent_polylist(Client::Badauthstage);
    } else {
        emit sent_polylist(Client::OK);
    }
}

void Client::sendsum_handler(const QString arguments)
{
    if (arguments == QString("BADPROCEDURE")) {
        emit sent_sum(Client::Badprocedure);
    } else if (arguments == QString("BADSTAGE")) {
        emit sent_sum(Client::Badstage);
    } else if (arguments == QString("BADAUTHSTAGE")) {
        emit sent_sum(Client::Badauthstage);
    } else if (arguments == QString("BADUSER")) {
        emit sent_sum(Client::Baduser);
    } else if (arguments == QString("DUPLICATE")) {
        emit sent_sum(Client::Duplicate);
    } else {
        emit sent_sum(Client::OK);
    }
}

void Client::sendvote_handler(const QString arguments)
{
    if (arguments == QString("BADPROCEDURE")) {
        emit sent_vote(Client::Badprocedure);
    } else if (arguments == QString("BADSTAGE")) {
        emit sent_vote(Client::Badstage);
    } else if (arguments == QString("BADVOTE")) {
        emit sent_vote(Client::Badvote);
    } else if (arguments == QString("BADUSER")) {
        emit sent_vote(Client::Baduser);
    } else if (arguments == QString("DUPLICATE")) {
        emit sent_vote(Client::Duplicate);
    } else if (arguments == QString("BADPROOF")) {
        emit sent_vote(Client::Badproof);
    } else if (arguments == QString("INVALIDPROOF")) {
        emit sent_vote(Client::Invalidproof);
    } else {
        emit sent_vote(Client::OK);
    }
}

void Client::startprocedure_handler(const QString arguments)
{
    if (arguments == QString("BADPROCEDURE")) {
        emit start_procedure(Client::Badprocedure);
    } else if (arguments == QString("BADSTAGE")) {
        emit start_procedure(Client::Badstage);
    } else {
        emit start_procedure(Client::OK);
    }
}

void Client::stopprocedure_handler(const QString arguments)
{
    if (arguments == QString("BADPROCEDURE")) {
        emit reset_procedure(Client::Badprocedure);
    } else if (arguments == QString("BADSTAGE")) {
        emit reset_procedure(Client::Badstage);
    } else {
        emit reset_procedure(Client::OK);
    }
}

void Client::user_handler(const QString arguments)
{
    if (arguments == QString("BADPROCEDURE")) {
        emit logged_in(Client::Badprocedure, false);
    } else if (arguments == QString("BADUSER")) {
        emit logged_in(Client::Baduser, false);
    } else if (arguments == QString("BADSTAGE")) {
        emit logged_in(Client::Badstage, false);
    } else {
        QRegExp rx("^\\s(\\d)\\s*\"(.*)\"\\s*$");
        rx.setMinimal(true);
        rx.exactMatch(arguments);
        bool is_authority = rx.capturedTexts().at(1).toInt();
        emit logged_in(Client::OK, is_authority);
    }
}

void Client::request_procedure_list()
{
    send_msg("GETPROCEDURELIST");
}

void Client::request_version()
{
    send_msg("VERSION \"1.0\"");
}

void Client::request_user_list()
{
    send_msg("GETUSERLIST");
}

void Client::create_procedure(const QString title, const QString text, 
                              const int threshold, const int pubkeytime,
                              const int polytime, const int seckeytime,
                              const int votetime,
                              const int keylength, const int robustness,
                              const int minchoices, const int maxchoices,
                              const std::vector<QString> choices,
                              const std::vector<QString> auths)
{
    QString command;
    command.append(QString("CREATEPROCEDURE \"%1\" \"%2\" %3 %4 %5 %6 %7 %8 %9 %10 %11 ")
                   .arg(title)
                   .arg(text)
                   .arg(threshold)
                   .arg(pubkeytime)
                   .arg(polytime)
                   .arg(seckeytime)
                   .arg(votetime)
                   .arg(keylength)
                   .arg(robustness)
                   .arg(minchoices)
                   .arg(maxchoices));

    QString choices_s = "(";
    for (unsigned int i = 0; i < choices.size(); i++) {
        choices_s.append(QString("\"%1\",").arg(choices[i]));
    }
    choices_s.chop(1); // Remove the trailing comma.
    choices_s.append(')');

    QString auth_s = "(";
    for (unsigned int i = 0; i < auths.size(); i++) {
        auth_s.append(QString("\"%1\",").arg(auths[i]));
    }
    auth_s.chop(1); // Remove the trailing comma.
    auth_s.append(')');

    command.append(QString("%1 %2")
                   .arg(choices_s)
                   .arg(auth_s));

    send_msg(command);
}

void Client::delete_procedure(const QString proc_id)
{
    send_msg(QString("DELETEPROCEDURE \"%1\"").arg(proc_id));
}

void Client::start_procedure(const QString proc_id)
{
    send_msg(QString("STARTPROCEDURE \"%1\"").arg(proc_id));
}

void Client::reset_procedure(const QString proc_id)
{
    send_msg(QString("STOPPROCEDURE \"%1\"").arg(proc_id));
}

void Client::get_title(const QString proc_id)
{
    send_msg(QString("GETTITLE \"%1\"").arg(proc_id));
}

void Client::get_choices(const QString proc_id)
{
    send_msg(QString("GETCHOICES \"%1\"").arg(proc_id));
}

void Client::get_description(const QString proc_id)
{
    send_msg(QString("GETDESCRIPTION \"%1\"").arg(proc_id));
}

void Client::get_key_constants(const QString proc_id)
{
    send_msg(QString("GETKEYCONSTANTS \"%1\"").arg(proc_id));
}

void Client::get_public_key(const QString proc_id)
{
    send_msg(QString("GETPUBKEY \"%1\"").arg(proc_id));
}

void Client::login(const QString username, const QString password, 
                   const QString proc_id)
{
    send_msg(QString("USER \"%1\" \"%2\" \"%3\"")
             .arg(username)
             .arg(password)
             .arg(proc_id));
}

void Client::send_public_key(const QString pub_key, const QString proc_id)
{
    send_msg(QString("SENDPUBLICKEY \"%1\" \"%2\"")
             .arg(pub_key)
             .arg(proc_id));
}

void Client::advance_procedure(const QString proc_id)
{
    send_msg(QString("PROGRESSPROCEDURE \"%1\"").arg(proc_id));
}

void Client::get_auth_pubkeys(const QString proc_id)
{
    send_msg(QString("GETAUTHPUBKEYS \"%1\"").arg(proc_id));
}

void Client::send_polylist(std::vector< std::pair<QString, QString> > poly_vec,
                           std::vector< std::pair<int, QString> > gvalue_vec,
                           QString proc_id)
{
    QString poly_str("(");
    vector< pair<QString, QString> >::iterator p_iter;
    for (p_iter = poly_vec.begin(); p_iter != poly_vec.end(); p_iter++) {
        poly_str += "(\"" + p_iter->first + "\",\"" + p_iter->second + "\"),";
    }
    poly_str.chop(1);
    poly_str += ')';

    QString gvalue_str("(");
    vector< pair<int, QString> >::iterator g_iter;
    for (g_iter = gvalue_vec.begin(); g_iter != gvalue_vec.end(); g_iter++) {
        gvalue_str += "(" + QString::number(g_iter->first) 
            + ",\"" + g_iter->second + "\"),";
    }
    gvalue_str.chop(1);
    gvalue_str += ')';

    send_msg(QString("SENDPOLYLIST %1 %2 \"%3\"")
             .arg(poly_str)
             .arg(gvalue_str)
             .arg(proc_id));
}

void Client::get_private_key_list(const QString proc_id)
{
    send_msg(QString("GETPRIVKEYLIST \"%1\"").arg(proc_id));
}

void Client::send_vote(const QString vote, const QString proof, 
                       const QString proc_id)
{
    send_msg(QString("SENDVOTE \"%1\" \"%2\" \"%3\"")
             .arg(vote)
             .arg(proof)
             .arg(proc_id));
}

void Client::get_num_votes(const QString proc_id)
{
    send_msg(QString("GETNUMVOTES \"%1\"").arg(proc_id));
}

void Client::get_cipher_sum(const QString proc_id)
{
    send_msg(QString("GETSUM \"%1\"").arg(proc_id));
}

void Client::send_sum(vector<adder::Integer> sum_vec, const QString proc_id)
{
    QString sum_str("(");
    vector<adder::Integer>::iterator s_iter;

    for (s_iter = sum_vec.begin(); s_iter != sum_vec.end(); s_iter++) {
        sum_str += QString(s_iter->str().c_str()) + ",";
    }

    sum_str.chop(1);
    sum_str += ')';

    send_msg(QString("SENDSUM %1 \"%2\"")
             .arg(sum_str)
             .arg(proc_id));
}

void Client::get_vote_list(const QString proc_id)
{
    send_msg(QString("GETVOTELIST \"%1\"").arg(proc_id));
}

void Client::get_vote(const QString proc_id, const QString user_id)
{
    send_msg(QString("GETVOTE \"%1\" \"%2\"")
             .arg(proc_id)
             .arg(user_id));
}

void Client::get_ballot_proof(const QString proc_id, const QString user_id)
{
    send_msg(QString("GETBALLOTPROOF \"%1\" \"%2\"")
             .arg(proc_id)
             .arg(user_id));
}

void Client::get_num_choices(const QString proc_id)
{
    send_msg(QString("GETNUMCHOICES \"%1\"").arg(proc_id));
}

void Client::get_results(const QString proc_id)
{
    send_msg(QString("GETRESULTS \"%1\"").arg(proc_id));
}

void Client::admin(const QString password)
{
    send_msg(QString("ADMIN \"%1\"").arg(password));
}

void Client::make_user(const QString username,
                       const QString password,
                       const QString first_name,
                       const QString middle_name,
                       const QString last_name,
                       const QString email)
{
    send_msg(QString("MAKEUSER \"%1\" \"%2\" \"%3\" \"%4\" \"%5\" \"%6\"")
             .arg(username)
             .arg(password)
             .arg(first_name)
             .arg(middle_name)
             .arg(last_name)
             .arg(email));
}

bool Client::is_connected() const
{
    return (socket->state() == QAbstractSocket::ConnectedState);
}
