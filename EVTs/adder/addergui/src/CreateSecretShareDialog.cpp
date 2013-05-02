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

#include <iostream>
#include <string>

#include "PublicKey.h"
#include "PrivateKey.h"
#include "Context.h"
#include "exceptions.h"

#include "CreateSecretShareDialog.h"
#include "Client.h"

#include "key_management.h"

using namespace std;
using namespace adder;

CreateSecretShareDialog::CreateSecretShareDialog(Client* client,
                                                 Procedure proc, 
                                                 QString user_id, QWidget *parent)
    : QDialog(parent), client(client), proc(proc), user_id(user_id)
{
    setAttribute(Qt::WA_DeleteOnClose);
    ui.setupUi(this);

    connect(client, SIGNAL(got_auth_pubkeys(Client::Error, std::vector< std::pair<int, std::string> >)),
            this, SLOT(got_auth_pubkeys(Client::Error, std::vector< std::pair<int, std::string> >)));
    
    connect(client, SIGNAL(sent_polylist(Client::Error)),
            this, SLOT(sent_polylist(Client::Error)));

    client->get_auth_pubkeys(proc.get_id().c_str());
}

void CreateSecretShareDialog::got_auth_pubkeys(Client::Error error,
                                               std::vector< std::pair<int, std::string> >
                                               key_vec)
{
    Context* context = new Context(true);
    PublicKey tmp_key(context);
    vector< pair<int, string> >::iterator i;

    switch(error) {
    case Client::Badprocedure:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Procedure does not exist."));
        break;
    case Client::Badstage:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Authority public keys have not\n"
                                 "yet been submitted."));
        break;
    case Client::OK:
        for (i = key_vec.begin(); i < key_vec.end(); i++) {
            tmp_key.from_str(i->second);
            auth_key_map[i->first] = tmp_key;
        }

        ui.generatePushButton->setEnabled(true);
        break;
    default:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Unknown error getting authority\n"
                                 "public keys"));
    }
}

void CreateSecretShareDialog::on_generatePushButton_clicked()
{
    Context context(true);
    adder::PublicKey pub_key;
    pub_key = read_public_key(user_id, QString(proc.get_id().c_str()),
                              &context);

    adder::Polynomial P(&context,
                        pub_key.get_p(),
                        pub_key.get_g(),
                        pub_key.get_f());
    
    P.gen_rand_coeffs(proc.get_threshold() - 1, pub_key.get_p());

    write_polynomial(P, user_id, QString(proc.get_id().c_str()));

    map<int, PublicKey>::iterator i;

    vector< pair<QString, QString> > poly_vec;
    vector< pair<int, QString> > gvalue_vec;

    for (i = auth_key_map.begin(); i != auth_key_map.end(); i++) {
        Integer q = (i->second.get_p() - 1) / 2;
        ElgamalCiphertext poly = i->second.encrypt_poly(P.evaluate(Integer(i->first, q)));
        poly_vec.push_back(pair<QString, QString>(QString::number(i->first), 
                                                  poly.str().c_str()));
    }

    for (unsigned int i = 0; i < P.coeffs.size(); i++) {
        gvalue_vec.push_back(pair<int, QString>
                             (i, P.get_g().pow(P.coeffs[i]).str().c_str()));
    }

    client->send_polylist(poly_vec, gvalue_vec, proc.get_id().c_str());
}

void CreateSecretShareDialog::sent_polylist(Client::Error error)
{
    switch(error) {
    case Client::Badprocedure:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Error submitting secret share information:\n"
                                 "Procedure not found."));
        break;
    case Client::Baduser:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Error submitting secret share information:\n"
                                 "Not authenticated."));
        break;
    case Client::Badstage:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Error submitting secret share information:\n"
                                 "You may not submit secret share information\n"
                                 "at this stage."));
        break;
        /*    case Client::Duplicate:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Error submitting secret share information:\n"
                                 "You have already submitted a\n"
                                 "secret share information."));
                                 break;*/
    case Client::Badpolylist:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Error submitting secret share information:\n"
                                 "This secret share information is malformed."));
        break;
    case Client::OK:
        QMessageBox::information(this, tr("AdderGUI"),
                                 tr("Secret share information submitted successfully."));
        accept();
        break;
    default:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Unknown error submitting\n"
                                 "secret share information"));
        break;
    }
}
