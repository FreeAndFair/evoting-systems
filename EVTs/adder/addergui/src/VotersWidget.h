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

#ifndef VOTERSWIDGET_H
#define VOTERSWIDGET_H

#include "ui_voterswidget.h"
#include "Client.h"
#include "Procedure.h"

class VotersWidget : public QWidget
{
    Q_OBJECT
    
public:
    VotersWidget(Procedure proc, Client* client, QWidget* parent = 0);
    
private slots:
    void on_votersTreeWidget_itemActivated(QTreeWidgetItem* item, int);
    void got_vote_list(Client::Error error,
                       std::vector< std::pair<std::string, std::string> > vote_vec);
    void on_viewPushButton_clicked();
    void on_votersTreeWidget_itemSelectionChanged();

private:
    Ui::VotersWidget ui;

    Procedure proc;
    Client* client;
};

#endif // VOTERSWIDGET_H
