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

#ifndef CONSOLEDIALOG_H
#define CONSOLEDIALOG_H

#include "ui_consoledialog.h"
#include "Client.h"

class ConsoleDialog : public QDialog
{
    Q_OBJECT
    
public:
    ConsoleDialog(Client* client, QWidget* parent = 0);
    
public slots:
    void got_message(const QString &line);
    void on_sendPushButton_clicked();
    void sending_message(const QString &line);
    void on_messageLineEdit_textChanged(const QString &text);
    
private:
    Ui::ConsoleDialog ui;

    Client* client;
};

#endif // CONSOLEDIALOG_H
