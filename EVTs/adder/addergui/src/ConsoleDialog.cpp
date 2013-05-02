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

#include "ConsoleDialog.h"
#include "Client.h"

using namespace std;

ConsoleDialog::ConsoleDialog(Client* client, QWidget* parent)
    : QDialog(parent), client(client)
{
    ui.setupUi(this);

    connect(client, SIGNAL(got_message(const QString &)),
            this, SLOT(got_message(const QString &)));
    connect(client, SIGNAL(sending_message(const QString &)),
            this, SLOT(sending_message(const QString &)));

    connect(ui.clearPushButton, SIGNAL(clicked()),
            ui.consoleTextEdit, SLOT(clear()));
}

void ConsoleDialog::got_message(const QString &line)
{
    ui.consoleTextEdit
        ->append("[" + 
                          QDateTime::currentDateTime()
                          .time().toString() + "] "
                 + "<b>server:</b> " + line);
}

void ConsoleDialog::on_sendPushButton_clicked()
{
    if (client->is_connected()) {
        client->send_msg(ui.messageLineEdit->text());
    } else {
        ui.consoleTextEdit->append("<b>Not connected!</b><br>");
    }

    ui.messageLineEdit->clear();
}

void ConsoleDialog::sending_message(const QString &line)
{
    ui.consoleTextEdit
        ->append("[" + 
                          QDateTime::currentDateTime()
                          .time().toString() + "] "
                 + "<b>client:</b> " + line);
}

void ConsoleDialog::on_messageLineEdit_textChanged(const QString &text)
{
    ui.sendPushButton->setEnabled(!text.isEmpty());
}
