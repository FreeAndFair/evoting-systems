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

#ifndef STATUSDIALOG_H
#define STATUSDIALOG_H

#include <vector>

#include "Client.h"
#include "Procedure.h"

#include "ui_statusdialog.h"

class StatusDialog : public QDialog
{
    Q_OBJECT
    
public:
    StatusDialog(Procedure proc, Client* client, QWidget* parent = 0);

private slots:
    void got_description(QString description);
    void got_choices(std::vector<QString> choices_vec);
    void got_results(Client::Error error, 
                     std::vector< std::pair<std::string, int> > results_vec);
    void got_public_key(Client::Error error, QString public_key);
    
private:
    Ui::StatusDialog ui;
    Procedure proc;
    Client* client;
};

#endif // STATUSDIALOG_H
