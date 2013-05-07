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

#include "VotersWidget.h"
#include "ViewVoterDialog.cpp"
#include "Client.h"
#include "Procedure.h"

using namespace std;

VotersWidget::VotersWidget(Procedure proc, Client* client, QWidget *parent)
    : QWidget(parent), proc(proc), client(client)
{
    //    setAttribute(Qt::WA_DeleteOnClose);

    connect(client, 
            SIGNAL(got_vote_list(Client::Error,
                                 std::vector< std::pair<std::string, std::string> >)),
            this, 
            SLOT(got_vote_list(Client::Error,
                          std::vector< std::pair<std::string, std::string> >)));

    client->get_vote_list(proc.get_id().c_str());

    ui.setupUi(this);
}

void VotersWidget::on_votersTreeWidget_itemActivated(QTreeWidgetItem* item, int)
{
    ViewVoterDialog* view_dialog = 
        new ViewVoterDialog(proc, client, item->text(0), this);

    view_dialog->show();
}

void VotersWidget::on_viewPushButton_clicked()
{
    QList<QTreeWidgetItem*> item_list = ui.votersTreeWidget->selectedItems();
    QTreeWidgetItem* item = item_list.at(0);

    on_votersTreeWidget_itemActivated(item, 0);
}

void VotersWidget::on_votersTreeWidget_itemSelectionChanged()
{
    QList<QTreeWidgetItem*> item_list = ui.votersTreeWidget->selectedItems();
    QTreeWidgetItem* item = item_list.at(0);

    ui.viewPushButton->setEnabled(item_list.size() != 0);
}

void VotersWidget::got_vote_list(Client::Error error,
                                 std::vector< std::pair<std::string, std::string> > vote_vec)
{
    ui.votersTreeWidget->clear();

    vector< pair<string, string> >::iterator i;
    for (i = vote_vec.begin(); i != vote_vec.end(); i++) {
        QTreeWidgetItem* item = new QTreeWidgetItem(ui.votersTreeWidget);

        item->setText(0, i->first.c_str());
        item->setText(1, i->second.c_str());
    }
}
