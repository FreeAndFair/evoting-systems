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

#include "SimpleWizard.h"
#include <iostream>

using namespace std;

SimpleWizard::SimpleWizard(QWidget *parent)
    : QDialog(parent)
{
    cancelButton = new QPushButton(tr("Cancel"));
    backButton = new QPushButton(tr("< &Back"));
    nextButton = new QPushButton(tr("Next >"));
    finishButton = new QPushButton(tr("&Finish"));

    connect(cancelButton, SIGNAL(clicked()), this, SLOT(reject()));
    connect(backButton, SIGNAL(clicked()), this, SLOT(backButtonClicked()));
    connect(nextButton, SIGNAL(clicked()), this, SLOT(nextButtonClicked()));
    connect(finishButton, SIGNAL(clicked()), this, SLOT(accept()));

    buttonLayout = new QHBoxLayout;
    buttonLayout->addStretch(1);
    buttonLayout->addWidget(cancelButton);
    buttonLayout->addWidget(backButton);
    buttonLayout->addWidget(nextButton);
    buttonLayout->addWidget(finishButton);

    mainLayout = new QVBoxLayout;
    mainLayout->addLayout(buttonLayout);
    setLayout(mainLayout);
}

void SimpleWizard::setButtonEnabled(bool enable)
{
    if (history.size() == numPages) {
        finishButton->setEnabled(enable);
    } else {
        nextButton->setEnabled(enable);
    }
}

void SimpleWizard::setNumPages(int n)
{
    numPages = n;
    history.append(createPage(0));
    switchPage(0);
}

void SimpleWizard::backButtonClicked()
{
    nextButton->setEnabled(true);
    finishButton->setEnabled(true);

    QWidget *oldPage = history.takeLast();
    switchPage(oldPage);
    delete oldPage;
}

void SimpleWizard::nextButtonClicked()
{
    QWidget *oldPage = history.last();
    history.append(createPage(history.size()));
    switchPage(oldPage);
}

void SimpleWizard::switchPage(QWidget *oldPage)
{
    if (oldPage) {
        oldPage->hide();
        mainLayout->removeWidget(oldPage);
    }

    QWidget *newPage = history.last();
    mainLayout->insertWidget(0, newPage);
    newPage->show();
    newPage->setFocus();

    backButton->setEnabled(history.size() != 1);
    if (history.size() == numPages) {
        nextButton->setEnabled(false);
        //        finishButton->setDefault(true);
    } else {
        nextButton->setDefault(true);
        finishButton->setEnabled(false);
    }

    setWindowTitle(tr("Procedure Creation Wizard - Step %1 of %2")
                   .arg(history.size())
                   .arg(numPages));
}
