#ifndef MAINWINDOW_H
#define MAINWINDOW_H

#include <QMainWindow>

namespace Ui {
    class MainWindow;
}

class MainWindow : public QMainWindow {
    Q_OBJECT
public:
    MainWindow(QWidget *parent = 0);
    ~MainWindow();

protected:
    void changeEvent(QEvent *e);
private Q_SLOTS:
    void on_saveButton_clicked();
    void on_cancelButton_clicked();
    void cancel();
    void validate();
    void saveVote();
private:
    Ui::MainWindow *ui;
};

#endif // MAINWINDOW_H
