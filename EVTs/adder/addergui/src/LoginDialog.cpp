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

#include "LoginDialog.h"
#include "Client.h"

using namespace std;

LoginDialog::LoginDialog(Client* client, QString proc_id, QString* user_id,
                         QString* password, QWidget *parent)
    : QDialog(parent), client(client), proc_id(proc_id), user_id(user_id), password(password)
{
    setAttribute(Qt::WA_DeleteOnClose);
    ui.setupUi(this);

    connect(client, SIGNAL(logged_in(Client::Error, bool)),
            this, SLOT(logged_in(Client::Error, bool)));
}

void LoginDialog::on_loginPushButton_clicked()
{
    client->login(ui.usernameLineEdit->text(), ui.passwordLineEdit->text(), 
                  proc_id);
}

void LoginDialog::logged_in(Client::Error error, bool)
{
    switch (error) {
    case Client::Baduser:
        QMessageBox::warning(this, tr("AdderGUI"),
                              tr("Invalid username or password."));
        break;
    case Client::Badstage:
        QMessageBox::warning(this, tr("AdderGUI"),
                             tr("You are not permitted to log in\n"
                                "at this stage.  Perhaps you are\n"
                                "not an authority."));
        break;
    case Client::OK:
        *user_id = ui.usernameLineEdit->text();
        *password = ui.passwordLineEdit->text();
        done(QDialog::Accepted);
        break;
    default:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Unknown error."));
    }
}
