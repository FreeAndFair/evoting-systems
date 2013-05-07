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

#ifndef PROCWIZARD_H
#define PROCWIZARD_H

#include <vector>

#include "ui_procwizardtitlepage.h"
#include "ui_procwizardthresholdpage.h"
#include "ui_procwizarddeadlinespage.h"
#include "ui_procwizardchoicespage.h"

#include "SimpleWizard.h"
#include "Client.h"

class QCheckBox;
class QGroupBox;
class QLabel;
class QLineEdit;
class QRadioButton;
class FirstPage;
class SecondPage;
class ThirdPage;
class FourthPage;

class ProcWizard : public SimpleWizard
{
    Q_OBJECT

public:
    ProcWizard(Client* client, QWidget *parent = 0);

protected:
    QWidget *createPage(int index);
    void accept();

private:
    FirstPage *firstPage;
    SecondPage *secondPage;
    ThirdPage *thirdPage;
    FourthPage *fourthPage;

    Client* client;

    friend class FirstPage;
    friend class SecondPage;
    friend class ThirdPage;
    friend class FourthPage;
};

class FirstPage : public QWidget
{
    Q_OBJECT

public:
    FirstPage(ProcWizard *wizard);
    
private slots:
    void titleChanged();

private:
    Ui::ProcWizardTitlePage ui;

    friend class ProcWizard;
    friend class SecondPage;
    friend class ThirdPage;
};

class SecondPage : public QWidget
{
    Q_OBJECT

public:
    SecondPage(ProcWizard *wizard);

private slots:
    void refresh_user_list(std::vector<std::string>);
    void on_addPushButton_clicked();
    void on_removePushButton_clicked();
    void validate_input();

private:
    Ui::ProcWizardThresholdPage ui;
    friend class ProcWizard;
};

class ThirdPage : public QWidget
{
    Q_OBJECT

public:
    ThirdPage(ProcWizard *wizard);

private:
    Ui::ProcWizardDeadlinesPage ui;

    friend class ProcWizard;
    friend class SecondPage;
    friend class FourthPage;
};

class FourthPage : public QWidget
{
    Q_OBJECT

public:
    FourthPage(ProcWizard *wizard);

private slots:
    void on_addPushButton_clicked();
    void on_removePushButton_clicked();
    void text_changed();

private:
    Ui::ProcWizardChoicesPage ui;

    friend class ProcWizard;
};

#endif // PROCWIZARD_H
