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
#include <list>
#include <algorithm>

#include "StatusDialog.h"
#include "VotersWidget.h"

using namespace std;

StatusDialog::StatusDialog(Procedure proc, Client* client, QWidget *parent)
    : QDialog(parent), proc(proc), client(client)
{
    setAttribute(Qt::WA_DeleteOnClose);
    ui.setupUi(this);

    setWindowTitle("Procedure Status - " + QString(proc.get_title().c_str()));

    connect(client, SIGNAL(got_description(QString)), 
            this, SLOT(got_description(QString)));
    connect(client, SIGNAL(got_choices(std::vector<QString>)),
            this, SLOT(got_choices(std::vector<QString>)));
    connect(client, SIGNAL(got_results(Client::Error,
                                       std::vector< std::pair<std::string, int> >)),
            this, SLOT(got_results(Client::Error,
                                   std::vector< std::pair<std::string, int> >)));
    connect(client, SIGNAL(got_public_key(Client::Error, QString)),
            this, SLOT(got_public_key(Client::Error, QString)));

    VotersWidget* v = new VotersWidget(proc, client, this);

    ui.tabWidget->insertTab(3, v, QString("Voters"));

    client->get_description(proc.get_id().c_str());
    client->get_choices(proc.get_id().c_str());
    client->get_results(proc.get_id().c_str());
    client->get_public_key(proc.get_id().c_str());

    if (proc.get_stage() == Procedure::STAGE_FINISHED) {
        ui.choicesLabel->setText("Results:");
        QPalette palette = ui.choicesTreeWidget->palette();
        palette.setColor(QPalette::Base,
                         QColor(255, 255, 200));
        ui.choicesTreeWidget->setPalette(palette);
    }
}

void StatusDialog::got_choices(std::vector<QString> choices_vec)
{
    for (unsigned int i = 0; i < choices_vec.size(); i++) {
        QTreeWidgetItem* item = new QTreeWidgetItem(ui.choicesTreeWidget);
        item->setText(0, choices_vec[i]);
    }
    
    ui.choicesTreeWidget->resizeColumnToContents(0);
}

void StatusDialog::got_description(QString description)
{
    ui.questionTextEdit->insertPlainText(description);
}

void StatusDialog::got_results(Client::Error error,
                               std::vector< std::pair<std::string, int> > results_vec)
{
    std::vector< std::pair<std::string, int> >::iterator i;
    list<int> count_list;

    for (i = results_vec.begin(); i != results_vec.end(); i++) {
        count_list.insert(count_list.end(), i->second);
    }

    list<int>::iterator max_iter = max_element(count_list.begin(), count_list.end());

    for (i = results_vec.begin(); i != results_vec.end(); i++) {
        QList<QTreeWidgetItem*> item_list = 
            ui.choicesTreeWidget->findItems(i->first.c_str(), Qt::MatchExactly);
        item_list.at(0)->setText(2, QString::number(i->second));
        item_list.at(0)->setTextAlignment(2, Qt::AlignRight);
        if (i->second == *max_iter) {
            item_list.at(0)->setIcon(1, QIcon(":/images/check.png"));
            item_list.at(0)->setTextAlignment(1, Qt::AlignRight);
        }
    }
}

void StatusDialog::got_public_key(Client::Error error, QString public_key)
{
    ui.pubkeyTextBrowser->insertPlainText(public_key);
}
