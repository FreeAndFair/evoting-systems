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

#include "CreateUsersDialog.h"
#include "Client.h"

using namespace std;

CreateUsersDialog::CreateUsersDialog(Client* client, QWidget *parent)
    : QDialog(parent), client(client)
{
    setAttribute(Qt::WA_DeleteOnClose);
    ui.setupUi(this);

    connect(ui.singleRadioButton, SIGNAL(toggled(bool)), SLOT(set_widgets_focus()));

    connect(client, SIGNAL(make_user(Client::Error)), SLOT(make_user(Client::Error)));
    connect(ui.createPushButton, SIGNAL(clicked()), SLOT(send_make_user()));
}

void CreateUsersDialog::set_widgets_focus()
{
    ui.singleGroupBox->setEnabled(ui.singleRadioButton->isChecked());
    ui.batchGroupBox->setEnabled(ui.batchRadioButton->isChecked());
}

void CreateUsersDialog::send_make_user()
{
    if (ui.passwordLineEdit->text() != ui.verifyLineEdit->text()) {
        QMessageBox::warning(this, tr("AdderGUI"),
                             tr("Passwords do not match."));
    } else {
        client->make_user(ui.usernameLineEdit->text(),
                          ui.passwordLineEdit->text(),
                          ui.firstLineEdit->text(),
                          ui.middleLineEdit->text(),
                          ui.lastLineEdit->text(),
                          ui.emailLineEdit->text());
    }
}

void CreateUsersDialog::make_user(Client::Error error)
{
    switch (error) {
    case Client::Duplicate:
        QMessageBox::warning(this, tr("AdderGUI"),
                              tr("A user with this username already exists"));
        break;
    case Client::OK:
        QMessageBox::information(this, tr("AdderGUI"),
                                 tr("User created successfully."));
        done(QDialog::Accepted);
        break;
    default:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Unknown error."));
    }
}
