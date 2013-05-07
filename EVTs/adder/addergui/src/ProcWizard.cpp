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
#include <vector>

#include "ProcWizard.h"

using namespace std;

ProcWizard::ProcWizard(Client* client, QWidget *parent)
    : SimpleWizard(parent)
{
    this->client = client;
    resize(600, 400);
    setNumPages(4);
}

QWidget *ProcWizard::createPage(int index)
{
    switch (index) {
    case 0:
        firstPage = new FirstPage(this);
        return firstPage;
    case 1:
        secondPage = new SecondPage(this);
        return secondPage;
    case 2:
        thirdPage = new ThirdPage(this);
        return thirdPage;
    case 3:
        fourthPage = new FourthPage(this);
        return fourthPage;
    }
    return 0;
}

void ProcWizard::accept()
{
    int pubkey_secs = thirdPage->ui.pubkeyhoursSpinBox->value() * 3600
        + thirdPage->ui.pubkeyminutesSpinBox->value() * 60 +
        + thirdPage->ui.pubkeysecondsSpinBox->value();

    int secshare_secs = thirdPage->ui.secsharehoursSpinBox->value() * 3600
        + thirdPage->ui.secshareminutesSpinBox->value() * 60 +
        + thirdPage->ui.secsharesecondsSpinBox->value();

    int seckey_secs = thirdPage->ui.seckeyhoursSpinBox->value() * 3600
        + thirdPage->ui.seckeyminutesSpinBox->value() * 60 +
        + thirdPage->ui.seckeysecondsSpinBox->value();

    int ballot_secs = thirdPage->ui.ballothoursSpinBox->value() * 3600
        + thirdPage->ui.ballotminutesSpinBox->value() * 60 +
        + thirdPage->ui.ballotsecondsSpinBox->value();

    std::vector<QString> choices;
    std::vector<QString> auths;

    for (int i = 0; i < fourthPage->ui.choicesListWidget->count(); i++) {
        choices.push_back(fourthPage->ui.choicesListWidget->item(i)->text());
    }

    for (int i = 0; i < secondPage->ui.authListWidget->count(); i++) {
        auths.push_back(secondPage->ui.authListWidget->item(i)->text());
    }

    client->create_procedure(firstPage->ui.titleLineEdit->text(),
                             fourthPage->ui.questionTextEdit->toPlainText(),
                             secondPage->ui.thresholdSpinBox->value(),
                             pubkey_secs, secshare_secs, seckey_secs,
                             ballot_secs, 1024, 
                             secondPage->ui.robustnessSpinBox->value(),
                             fourthPage->ui.minimumSpinBox->value(),
                             fourthPage->ui.maximumSpinBox->value(),
                             choices, auths);
    QDialog::accept();
}

FirstPage::FirstPage(ProcWizard *wizard)
    : QWidget(wizard)
{
    ui.setupUi(this);

    wizard->setButtonEnabled(false);

    connect(ui.titleLineEdit, SIGNAL(textChanged(const QString &)),
            this, SLOT(titleChanged()));

    QRegExp rxp("[^\"]+");
    QValidator* validator = new QRegExpValidator(rxp, this);
    ui.titleLineEdit->setValidator(validator);
}

void FirstPage::titleChanged()
{
    ProcWizard* wizard = qobject_cast<ProcWizard*>(parent());
    wizard->setButtonEnabled(!ui.titleLineEdit->text().isEmpty());
}

SecondPage::SecondPage(ProcWizard *wizard)
    : QWidget(wizard)
{
    ui.setupUi(this);

    wizard->setButtonEnabled(false);

    connect(wizard->client, SIGNAL(got_user_list(std::vector<std::string>)),
            this, SLOT(refresh_user_list(std::vector<std::string>)));
    connect(ui.thresholdSpinBox, SIGNAL(valueChanged(int)),
            this, SLOT(validate_input()));
    connect(ui.robustnessSpinBox, SIGNAL(valueChanged(int)),
            this, SLOT(validate_input()));
    
    wizard->client->request_user_list();
}

void SecondPage::on_addPushButton_clicked()
{
    QList<QListWidgetItem*> auth_list = ui.userListWidget->selectedItems();

    for (int i = 0; i < auth_list.size(); i++) {
        if (!ui.authListWidget->findItems(auth_list.at(i)->text(), 
                                          Qt::MatchExactly).size()) {
            ui.authListWidget->addItem(auth_list.at(i)->text());
            delete auth_list.at(i);
        }
    }
    
    validate_input();
}

void SecondPage::on_removePushButton_clicked()
{
    QList<QListWidgetItem*> auth_list = ui.authListWidget->selectedItems();
    
    for (int i = 0; i < auth_list.size(); i++) {
        ui.userListWidget->addItem(auth_list.at(i)->text());
        delete auth_list.at(i);
    }

    validate_input();
}

void SecondPage::validate_input()
{
    ProcWizard* wizard = qobject_cast<ProcWizard*>(parent());
    wizard->setButtonEnabled(ui.authListWidget->count() >= 
                             ui.thresholdSpinBox->value()
                             * ui.robustnessSpinBox->value()); 
}

void SecondPage::refresh_user_list(std::vector<std::string> user_vec)
{
    for (unsigned int i = 0; i < user_vec.size(); i++) {
        new QListWidgetItem(QString(user_vec[i].c_str()), ui.userListWidget);
    }
}

ThirdPage::ThirdPage(ProcWizard *wizard)
    : QWidget(wizard)
{
    ui.setupUi(this);
}

FourthPage::FourthPage(ProcWizard *wizard)
    : QWidget(wizard)
{
    ui.setupUi(this);
    
    connect(ui.questionTextEdit, SIGNAL(textChanged()),
            this, SLOT(text_changed()));

    QRegExp rxp("[^\"]+");
    QValidator* validator = new QRegExpValidator(rxp, this);

    ui.newchoiceLineEdit->setValidator(validator);

    wizard->setButtonEnabled(false);
}

void FourthPage::on_addPushButton_clicked()
{
    if (!ui.choicesListWidget->findItems(ui.newchoiceLineEdit->text(), 
                                         Qt::MatchExactly).size()) {
        ui.choicesListWidget->addItem(ui.newchoiceLineEdit->text());
    } else {
        QMessageBox::information(this, tr("AdderGUI"), tr("This choice has already been added."));
    }
    
    ui.newchoiceLineEdit->clear();
    text_changed();
}

void FourthPage::on_removePushButton_clicked()
{
    QList<QListWidgetItem*> list = ui.choicesListWidget->selectedItems();
    
    for (int i = 0; i < list.size(); i++) {
        delete list.at(i);
    }

    text_changed();
}

void FourthPage::text_changed()
{
    ProcWizard* wizard = qobject_cast<ProcWizard*>(parent());
    wizard->setButtonEnabled(!ui.questionTextEdit->toPlainText().isEmpty() &&
                             !(ui.choicesListWidget->count() == 0));
}

