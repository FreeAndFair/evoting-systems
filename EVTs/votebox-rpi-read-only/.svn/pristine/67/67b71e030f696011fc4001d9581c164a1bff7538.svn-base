#include "mainwindow.h"
#include "ui_mainwindow.h"
#include <qfile.h>
#include <qmessagebox.h>
#include <QtGui>
#include <QFile>
#include <QDomDocument>
#include <QtXmlPatterns>
#include <iostream>
#include <string>

MainWindow::MainWindow(QWidget *parent) :
    QMainWindow(parent),
    ui(new Ui::MainWindow)
{
    //XML Ballot
    ui->setupUi(this);
    // Attempt to load in the XML ballot file
    QDomDocument doc("Ballot");
    QFile opmlFile("C:/Votebox/votebox/ballot.xml"); //ballot address

    // If it doesn't open, display error and exit
    if ( !opmlFile.open( QIODevice::ReadOnly ) ) {
        QMessageBox::critical( 0,tr( "Critical Error" ),tr( "Cannot open file!" ) );
        return;
    }

    // Once it's opened, try to parse it
    if(!doc.setContent(&opmlFile)){
        // If it won't parse, display error and exit
        opmlFile.close();
        QMessageBox::critical( 0,tr( "Critical Error" ),tr( "Ballot file is not valid XML!" ) );
        return;
    }

    // Check the root element of the xml is 'ballot'
    const QString ballotText(QString::fromUtf8(opmlFile.readAll()));
    validate(ballotText); //Schema Validater, this isn't meant to stop the program, but instead log a schema mismatch.
    //   of the incoming XML data
    QDomElement root=doc.documentElement();
    if(root.tagName() != "ballot"){
        QMessageBox::critical( 0,
                tr( "Critical Error" ),
                tr( "Ballot file is not a valid ballot!" ) );
        return;
    }
    // Begin reading through the XML data
    QDomNode n = root.firstChildElement();
    while(!n.isNull()){
        QDomNode x = n.firstChildElement();
        QDomElement e = n.toElement();
                QDomElement p = x.firstChildElement();//p finds Races and Initiative Tags
                QDomElement q = x.lastChildElement();//q finds Candidates
                if(e.tagName()=="races"){
                    ui->raceLabel->setText(p.text());
                    QDomElement z = q.firstChildElement();//Meant to construct a for or while loop below, kept getting mem leaks
                    if (!q.isNull()){//For loop would be better for this. Checks for candidates and then enters at least two names and parties.
                        ui->raceCand1->setText(z.firstChildElement().text());//Sets first candidate 
                        ui->partyLabel_1->setText(z.lastChildElement().text());//Sets first candidate's party
                        z = z.nextSiblingElement("candidate");//Moves to next candidate
                        ui->raceCand2->setText(z.firstChildElement().text());
                        ui->partyLabel_2->setText(z.lastChildElement().text());
                        if(!z.nextSibling().isNull()){
                            z = z.nextSiblingElement("candidate");
                            ui->raceCand3->setText(z.firstChildElement().text());
                            ui->partyLabel_3->setText(z.lastChildElement().text());
                            if(!z.nextSibling().isNull()){
                                z = z.nextSiblingElement("candidate");
                                ui->raceCand4->setText(z.firstChildElement().text());
                                ui->partyLabel_4->setText(z.lastChildElement().text());
                                if(!z.nextSibling().isNull()){
                                    z = z.nextSiblingElement("candidate");
                                    ui->raceCand5->setText(z.firstChildElement().text());
                                    ui->partyLabel_5->setText(z.lastChildElement().text());//This scope allows for 5 candidates, which is fine for a presidential ballot
                                }
                                else{
                                    ui->raceCand5->hide();
                                    ui->partyLabel_5->hide();
                                }
                            }
                            else{
                                ui->raceCand5->hide();
                                ui->partyLabel_5->hide();
                                ui->raceCand4->hide();
                                ui->partyLabel_4->hide();
                            }
                        }
                        else{
                            ui->raceCand5->hide();
                            ui->partyLabel_5->hide();
                            ui->raceCand4->hide();
                            ui->partyLabel_4->hide();
                            ui->raceCand3->hide();
                            ui->partyLabel_3->hide();
                        }
                    }
                    else{
                        QMessageBox::information(0,tr( "Alert" ),tr( "No Candidates Found" ));
                    }
                }
                if(e.tagName()=="initiatives"|| !e.isNull()){//checks for at least one proposition
                    ui->propBox1->setText(p.text());
                    ui->initLabel_1->setText(p.nextSiblingElement().text());
                    p = x.nextSiblingElement();
                    if(!x.isNull()){// Goes on to look for other propositions
                        x = x.nextSiblingElement();
                        ui->propBox2->setText(p.firstChildElement().text());
                        ui->initLabel_2->setText(p.lastChildElement().text());
                        if(true){
                            x = x.nextSiblingElement();
                            ui->propBox3->setText(x.firstChildElement().text());
                            ui->initLabel_3->setText(x.lastChildElement().text());
                            x = x.nextSiblingElement();
                            if(true){
                                x = x.nextSiblingElement();
                                ui->propBox4->setText(x.firstChildElement().text());
                                ui->initLabel_4->setText(x.lastChildElement().text());
                                if(true){
                                    x = x.nextSibling();
                                    ui->propBox5->setText(x.firstChildElement().text());
                                    ui->initLabel_5->setText(x.lastChildElement().text());
                                }
                                else{                                                       //Hides all unused proposition elements
                                    ui->propBox5->hide();
                                    ui->initLabel_5->hide();
                                }
                            }
                            else{
                                ui->propBox5->hide();
                                ui->initLabel_5->hide();
                                ui->propBox4->hide();
                                ui->initLabel_4->hide();
                            }
                        }
                        else{
//                            QMessageBox::information(0,tr( "Alert" ),tr( "Break Here second" ));
                            ui->propBox5->hide();
                            ui->initLabel_5->hide();
                            ui->propBox4->hide();
                            ui->initLabel_4->hide();
                            ui->propBox3->hide();
                            ui->initLabel_3->hide();
                        }
                    }
                    else{
                        QMessageBox::information(0,tr( "Alert" ),tr( "Break Here first" ));
                        ui->propBox5->hide();
                        ui->initLabel_5->hide();
                        ui->propBox4->hide();
                        ui->initLabel_4->hide();
                        ui->propBox3->hide();
                        ui->initLabel_3->hide();
                        ui->propBox2->hide();
                        ui->initLabel_2->hide();
                    }
                }
                else{
                    QMessageBox::information(0,tr( "Alert" ),tr( "No Propostions" ));   //if no props
                    ui->propBox1->hide();
                    ui->initLabel_1->hide();
                }
                n = n.nextSibling();
    }
}
void MainWindow::cancel()
{
delete ui;
}
void MainWindow::saveVote()
{
    //QObject::connect(ui->cancelButton())
}
MainWindow::~MainWindow()
{
    delete ui;
}

void MainWindow::changeEvent(QEvent *e)
{
    QMainWindow::changeEvent(e);
    switch (e->type()) {
    case QEvent::LanguageChange:
        ui->retranslateUi(this);
        break;
    default:
        break;
    }
}

void MainWindow::on_cancelButton_clicked()
{
    MainWindow::close();
}

void MainWindow::on_saveButton_clicked()
{
    QString cand;
    int prop1,prop2,prop3,prop4,prop5 = 0;// These gather info from the ballots that were casted.
    if (ui->candGroup->checkedButton()->isChecked()){
         cand = ui->candGroup->checkedButton()->text();//Will break if there is no candidate selected
    }
    if (ui->propBox1->isHidden()==false||ui->propBox1->isChecked()==true){ //These check which box was ticked by the voter
        prop1 = 1;
    }
    else{prop1=0;}
    if (ui->propBox2->isHidden()==false||ui->propBox2->isChecked()==true){
        prop2 = 1;
    }
    else{prop2=0;}
    if (ui->propBox3->isHidden()==false||ui->propBox3->isChecked()==true){
        prop3 = 1;
    }
    else{prop3=0;}
    if (ui->propBox4->isHidden()==false||ui->propBox4->isChecked()==true){
        prop4 = 1;
    }
    else{prop4=0;}
    if (ui->propBox1->isHidden()==false||ui->propBox5->isChecked()==true){
        prop5 = 1;
    }
    else{prop5=0;}
    QFile outBallot;
    //QFile numBallots;
    outBallot.setFileName("vote.txt");
    outBallot.open(QIODevice::WriteOnly);
    QTextStream vote(&outBallot);
    vote << "Vote for: " << cand << endl;
    vote << "Prop1: " << prop1 << "\n";
    vote << "Prop2: " << prop2 << "\n";
    vote << "Prop3: " << prop3 << "\n";
    vote << "Prop4: " << prop4 << "\n";
    vote << "Prop5: " << prop5 << "\n";
    QMessageBox::critical( 0,tr( "Critical Error" ),tr( "one vote for %1").arg(cand));
}
class MessageHandler : public QAbstractMessageHandler
{
    public:
        MessageHandler()
            : QAbstractMessageHandler(0)
        {
        }

        QString statusMessage() const
        {
            return m_description;
        }

        int line() const
        {
            return m_sourceLocation.line();
        }

        int column() const
        {
            return m_sourceLocation.column();
        }

    protected:
        virtual void handleMessage(QtMsgType type, const QString &description,
                                   const QUrl &identifier, const QSourceLocation &sourceLocation)
        {
            Q_UNUSED(type);
            Q_UNUSED(identifier);

            m_messageType = type;
            m_description = description;
            m_sourceLocation = sourceLocation;
        }

    private:
        QtMsgType m_messageType;
        QString m_description;
        QSourceLocation m_sourceLocation;
};
void MainWindow::validate(QString ballotText)//Schema Validator
{
    QFile schemaDoc("C:/Votebox/votebox/ballot.xsd");
    const QString schemaText(QString::fromUtf8(schemaDoc.readAll()));
    MessageHandler messageHandler;
    QXmlSchema schema;
    schema.setMessageHandler(messageHandler);
    const QByteArray schemaDataappend(ballotText);
    const QByteArray::append(schemaText);
    schema.load(schemaText);
}
