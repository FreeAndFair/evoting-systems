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
#include "VoteProof.h"
#include "exceptions.h"

#include "SelectChoiceDialog.h"
#include "Client.h"

#include "key_management.h"

using namespace std;

SelectChoiceDialog::SelectChoiceDialog(Client* client, Procedure proc, 
                                       QString user_id, QWidget *parent)
    : QDialog(parent), client(client), proc(proc), user_id(user_id)
{
    ui.setupUi(this);
    setAttribute(Qt::WA_DeleteOnClose);

    connect(client, SIGNAL(got_description(QString)), 
            this, SLOT(got_description(QString)));
    connect(client, SIGNAL(got_choices(std::vector<QString>)),
            this, SLOT(got_choices(std::vector<QString>)));
    connect(client, SIGNAL(got_public_key(Client::Error, QString)),
            this, SLOT(got_public_key(Client::Error, QString)));
    connect(client, SIGNAL(sent_vote(Client::Error)),
            this, SLOT(sent_vote(Client::Error)));

    progress = new QProgressDialog("Encrypting vote...", "Cancel", 0, 0, this);

    client->get_description(proc.get_id().c_str());
    client->get_choices(proc.get_id().c_str());
    client->get_public_key(proc.get_id().c_str());

    ui.minLabel->setText(QString::number(proc.get_minchoices()));
    ui.maxLabel->setText(QString::number(proc.get_maxchoices()));
}

void SelectChoiceDialog::got_choices(std::vector<QString> choices_vec)
{
    for (unsigned int i = 0; i < choices_vec.size(); i++) {
        new QListWidgetItem(choices_vec[i], ui.choicesListWidget);
    }
}

void SelectChoiceDialog::got_description(QString description)
{
    ui.questionTextBrowser->insertPlainText(description);
}

void SelectChoiceDialog::got_public_key(Client::Error, QString key)
{
    adder::Context* context = new adder::Context(true);
    public_key = new adder::PublicKey(context);
    
    try {
        public_key->from_str(key.toStdString());
        ui.submitPushButton->setEnabled(true);
    } catch(adder::Invalid_key) {
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Invalid public key."));
    }
    
}

void SelectChoiceDialog::on_submitPushButton_clicked()
{
    vector<bool> choices;
    for (int i = 0; i < ui.choicesListWidget->count(); i++) {
        choices.push_back(false);
    }
    
    QList<QListWidgetItem*> selected_items = ui.choicesListWidget->selectedItems();

    if (selected_items.size() < proc.get_minchoices() ||
        selected_items.size() > proc.get_maxchoices()) {
        QMessageBox::warning(this,
                             tr("AdderGUI"),
                             tr("You have selected an invalid number of choices."));
        return;
    }

    for (int i = 0; i < selected_items.size(); i++) {
        choices[ui.choicesListWidget->row(selected_items.at(i))] = true;
    }

    if (QMessageBox::information(this,
                                 tr("AdderGUI"),
                                 tr("Submit vote?"),
                                 tr("&Submit"), tr("Cancel"),
                                 QString(), 0, 1) == 0) {

        progress->setValue(1);
        adder::Vote v = public_key->encrypt(choices);
        progress->setLabelText("Computing proof...");

        adder::VoteProof proof;
        proof.compute(v, *public_key, choices, proc.get_minchoices(), 
                      proc.get_maxchoices());

        progress->setLabelText("Sending vote...");
        
        client->send_vote(v.str().c_str(),
                          proof.str().c_str(), 
                          proc.get_id().c_str());
    }
}

void SelectChoiceDialog::sent_vote(Client::Error error)
{
    progress->cancel();

    switch(error) {
    case Client::Badprocedure:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Error submitting vote:\n"
                                 "Procedure not found."));
        break;
    case Client::Baduser:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Error submitting vote:\n"
                                 "Not authenticated."));
        break;
    case Client::Badstage:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Error submitting vote:\n"
                                 "You may not submit a vote\n"
                                 "at this stage."));
        break;
    case Client::Duplicate:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Error submitting vote:\n"
                                 "You have already submitted a\n"
                                 "vote."));
        break;
    case Client::Badvote:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Error submitting vote:\n"
                                 "This vote is malformed."));
        break;
    case Client::Badproof:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Error submitting vote:\n"
                                 "The proof is malformed."));
        break;
    case Client::Invalidproof:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Error submitting vote:\n"
                                 "The proof is invalid."));
        break;
    case Client::OK:
        QMessageBox::information(this, tr("AdderGUI"),
                                 tr("Vote submitted successfully."));
        accept();
        break;
    default:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Error submitting vote:\n"
                                 "Procedure not found."));
        break;
    }
}
