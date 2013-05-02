/* -*- Mode: C++; tab-width: 4; indent-tabs-mode: nil; c-basic-offset: 4 -*- */
/*
 * Adder plugin for Mozilla
 * Copyright (C) 2004, 2005, 2006 The Adder Team
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA
 */

#include "key_management.h"

#ifndef WIN32
#include "errno.h"
#include "stdlib.h"
#include "sys/types.h"
#include "sys/stat.h"
#include "unistd.h"
#endif

#include <QtCore>
#include <QtCrypto>
#include <QtGui>
#include <QtDebug>

#include "common.h"
#include "Context.h"
#include "exceptions.h"
#include "PrivateKey.h"
#include "PublicKey.h"
#include "Vote.h"
#include "Polynomial.h"

#include <fstream>
#include <vector>
#include <string>
#include <sstream>
#include <iostream>

#define DIRSEP '/'

QString default_adder_directory()
{
    QString path = QDir::homePath();

#ifdef Q_WS_WIN
    path += "/Application Data/Adder";
#else
    path += "/.adder";
#endif

    return path;
}

bool create_key_directory(QString user, QString procedure)
{
    if (!is_valid_user(user) || !is_valid_procedure(procedure)) {
        return false;
    }

    QSettings settings;
    QString adderdir = settings.value("keys/key_dir", default_adder_directory()).toString();

    QString path = adderdir + '/' + procedure + '/' + user;
    qDebug() << "Creating directory: " << path;

    QDir dir(path);
    if (dir.exists(path)) {
        qDebug() << "Directory already exists.\n";
        return true;
    } else if (dir.mkpath(path)) {
        qDebug() << "Successfully created directory.\n";
        return true;
    } else {
        qDebug() << "Could not create directory.\n";
        return false;        
    }
}

adder::Vote encrypt_vote(adder::PublicKey key, std::vector<bool> choices)
{
    adder::Vote encrypted_vote = key.encrypt(choices);

    return encrypted_vote;
}

adder::PublicKey read_public_key(QString user, QString proc, adder::Context* context)
{
    QSettings settings;
    QString file_name = settings.value("keys/pubkey_file").toString();
    QString key_dir = settings.value("keys/key_dir").toString();

    QFile file(key_dir + '/' + proc + '/' + user + '/' + file_name);

    if (!file.open(QIODevice::ReadOnly | QIODevice::Text)) {
        throw Failed();
    } else {
        QTextStream in(&file);
        QString line = in.readLine();
        file.close();

        adder::PublicKey pub_key(context);
        
        try {
            pub_key.from_str(line.toStdString());
            return pub_key;
        } catch (adder::Invalid_key){
            throw Failed();
        }
    }
}

bool write_public_key(adder::PublicKey key, QString user, QString proc)
{
    QSettings settings;
    QString file_name = settings.value("keys/pubkey_file").toString();
    QString key_dir = settings.value("keys/key_dir").toString();

    QFile file(key_dir + '/' + proc + '/' + user + '/' + file_name);

    qDebug() << "Opening public key file";
    if (!file.open(QIODevice::WriteOnly | QIODevice::Truncate)) {
        qDebug() << "Could not open public key file";
        return false;
    } else {
        qDebug() << "Writing public key to file";
        QTextStream out(&file);
        out << key.str().c_str() << "\n";
        qDebug() << "Closing public key file";
        file.close();

        return true;
    }
}

// adder::Polynomial read_polynomial(QString key_file, adder::Context* context = NULL)
// {
//     std::ifstream infile(key_file.c_str());
    
//     QString key_str;
    
//     getline(infile, key_str);

//     infile.close();

//     adder::Polynomial poly(context);

//     try {
//         poly.load_from_armor(key_str);
//     } catch (adder::Invalid_polynomial) {
//         return poly;
//     }
    
//     return poly;
// }

bool write_polynomial(adder::Polynomial P, QString user, QString procedure)
{
    QSettings settings;
    QString file_name = settings.value("keys/polynomial_file").toString();
    QString key_dir = settings.value("keys/key_dir").toString();

    QFile file(key_dir + '/' + procedure + '/' + user + '/' + file_name);

    if (!file.open(QIODevice::WriteOnly | QIODevice::Truncate)) {
        return false;
    } else {
        QTextStream out(&file);
        out << P.str().c_str() << "\n";
        file.close();

        return true;
    }
}

adder::PrivateKey read_private_key(QString user, QString proc, QString password)
{
    QSettings settings;
    QString file_name = settings.value("keys/privkey_file").toString();
    QString key_dir = settings.value("keys/key_dir").toString();

    QFile file(key_dir + '/' + proc + '/' + user + '/' + file_name);

    if (!file.open(QIODevice::ReadOnly | QIODevice::Text)) {
        throw Failed();
    } else {
        QTextStream in(&file);

        qDebug() << "Loading initialization vector";
        QCA::InitializationVector iv(QCA::hexToArray(in.readLine()));
        qDebug() << "Read initialization vector";

        qDebug() << "Creating encryption key";
        QSecureArray key_array = password.leftJustified(16, ' ', true).toLatin1();
        qDebug() << "Key: " << password;
        QCA::SymmetricKey key(key_array);
        qDebug() << "Created encryption key";

        qDebug() << "Initializing cipher";
        QCA::AES128 cipher(QCA::Cipher::CBC,
                           QCA::Cipher::DefaultPadding,
                           QCA::Decode,
                           key, iv);
        qDebug() << "Initialized cipher";
        
        qDebug() << "Reading private key";
        QString line = in.readLine();
        file.close();
        qDebug() << "Read private key: " << line;

        qDebug() << "Loading ciphertext";
        QSecureArray ciphertext(QCA::hexToArray(line));
        qDebug() << "Decrypting";
        QSecureArray plaintext = cipher.process(ciphertext);
        qDebug() << "Decrypted";
        QString key_str(plaintext.data());
        qDebug() << "Key: " << key_str;

        adder::PrivateKey priv_key;
        qDebug() << "Loading private key";
        priv_key.from_str(key_str.toStdString());
        return priv_key;
    }
}

bool write_private_key(adder::PrivateKey priv_key, QString user, QString proc, 
                       QString password)
{
    QSettings settings;
    QString file_name = settings.value("keys/privkey_file").toString();
    QString key_dir = settings.value("keys/key_dir").toString();

    QFile file(key_dir + '/' + proc + '/' + user + '/' + file_name);

    qDebug() << "Opening private key file";

    if (!file.open(QIODevice::WriteOnly | QIODevice::Truncate)) {
        qDebug() << "Could not open private key file";
        return false;
    } else {
        qDebug() << "Initializing AES128";
        QCA::InitializationVector iv(16);
        
        QSecureArray key_array = password.leftJustified(16, ' ', true).toLatin1();

        QCA::SymmetricKey key(key_array);
        QCA::AES128 cipher(QCA::Cipher::CBC,
                           QCA::Cipher::DefaultPadding,
                           QCA::Encode,
                           key, iv);

        QSecureArray message(priv_key.str().c_str());

        qDebug() << "Updating AES128 with private key";
        QSecureArray u = cipher.update(message);

        if (!cipher.ok()) {
            qDebug() << "Update failed";
        } else {
            qDebug() << "Update succeeded";
        }

        qDebug() << "AES128 encryption of " << QString(priv_key.str().c_str()) << "is [" 
                 << qPrintable(QCA::arrayToHex(u)) << "]";
        
        qDebug() << "Finalizing AES128";
        QSecureArray f = cipher.final();

        if (!cipher.ok()) {
            qDebug() << "Finalize failed";
        } else {
            qDebug() << "Finalize succeeded";
        }

        qDebug() << "Writing private key to file";
        QTextStream out(&file);
        out << QCA::arrayToHex(iv);
        out << '\n';
        out << QCA::arrayToHex(u);
        out << QCA::arrayToHex(f);
        qDebug() << "Closing private key file";
        file.close();
    }

    return true;
}

adder::PrivateKey read_private_key2(QString user, QString proc, QString password)
{
    /* FIXME: Merge this and write_private_key2 with
       read/write_private_key somehow. */

//     QSettings settings;
//     QString file_name = settings.value("keys/privkey2_file").toString();
//     QString key_dir = settings.value("keys/key_dir").toString();

//     QFile file(key_dir + '/' + proc + '/' + user + '/' + file_name);

//     if (!file.open(QIODevice::ReadOnly | QIODevice::Text)) {
//         throw Failed();
//     } else {
//         QTextStream in(&file);
//         QString line = in.readLine();
//         file.close();

//         adder::PrivateKey priv_key;
//         priv_key.from_str(line.toStdString());
//         return priv_key;
//     }

    QSettings settings;
    QString file_name = settings.value("keys/privkey2_file").toString();
    QString key_dir = settings.value("keys/key_dir").toString();

    QFile file(key_dir + '/' + proc + '/' + user + '/' + file_name);

    if (!file.open(QIODevice::ReadOnly | QIODevice::Text)) {
        throw Failed();
    } else {
        QTextStream in(&file);

        qDebug() << "Loading initialization vector";
        QCA::InitializationVector iv(QCA::hexToArray(in.readLine()));
        qDebug() << "Read initialization vector";

        qDebug() << "Creating encryption key";
        QSecureArray key_array = password.leftJustified(16, ' ', true).toLatin1();
        qDebug() << "Key: " << password;
        QCA::SymmetricKey key(key_array);
        qDebug() << "Created encryption key";

        qDebug() << "Initializing cipher";
        QCA::AES128 cipher(QCA::Cipher::CBC,
                           QCA::Cipher::DefaultPadding,
                           QCA::Decode,
                           key, iv);
        qDebug() << "Initialized cipher";
        
        qDebug() << "Reading private key";
        QString line = in.readLine();
        file.close();
        qDebug() << "Read private key: " << line;

        qDebug() << "Loading ciphertext";
        QSecureArray ciphertext(QCA::hexToArray(line));
        qDebug() << "Decrypting";
        QSecureArray plaintext = cipher.process(ciphertext);
        qDebug() << "Decrypted";
        QString key_str(plaintext.data());
        qDebug() << "Key: " << key_str;

        adder::PrivateKey priv_key;
        qDebug() << "Loading private key";
        priv_key.from_str(key_str.toStdString());
        return priv_key;
    }
}

bool write_private_key2(adder::PrivateKey priv_key, QString user, QString proc,
                        QString password)
{
//     QSettings settings;
//     QString file_name = settings.value("keys/privkey2_file").toString();
//     QString key_dir = settings.value("keys/key_dir").toString();

//     QFile file(key_dir + '/' + proc + '/' + user + '/' + file_name);

//     if (!file.open(QIODevice::WriteOnly | QIODevice::Truncate)) {
//         return false;
//     } else {
//         QTextStream out(&file);
//         out << key.str().c_str() << "\n";
//         file.close();

//         return true;
//     }

    QSettings settings;
    QString file_name = settings.value("keys/privkey2_file").toString();
    QString key_dir = settings.value("keys/key_dir").toString();

    QFile file(key_dir + '/' + proc + '/' + user + '/' + file_name);

    qDebug() << "Opening private key file";

    if (!file.open(QIODevice::WriteOnly | QIODevice::Truncate)) {
        qDebug() << "Could not open private key file";
        return false;
    } else {
        qDebug() << "Initializing AES128";
        QCA::InitializationVector iv(16);
        
        QSecureArray key_array = password.leftJustified(16, ' ', true).toLatin1();

        QCA::SymmetricKey key(key_array);
        QCA::AES128 cipher(QCA::Cipher::CBC,
                           QCA::Cipher::DefaultPadding,
                           QCA::Encode,
                           key, iv);

        QSecureArray message(priv_key.str().c_str());

        qDebug() << "Updating AES128 with private key";
        QSecureArray u = cipher.update(message);

        if (!cipher.ok()) {
            qDebug() << "Update failed";
        } else {
            qDebug() << "Update succeeded";
        }

        qDebug() << "AES128 encryption of " << QString(priv_key.str().c_str()) << "is [" 
                 << qPrintable(QCA::arrayToHex(u)) << "]";
        
        qDebug() << "Finalizing AES128";
        QSecureArray f = cipher.final();

        if (!cipher.ok()) {
            qDebug() << "Finalize failed";
        } else {
            qDebug() << "Finalize succeeded";
        }

        qDebug() << "Writing private key to file";
        QTextStream out(&file);
        out << QCA::arrayToHex(iv);
        out << '\n';
        out << QCA::arrayToHex(u);
        out << QCA::arrayToHex(f);
        qDebug() << "Closing private key file";
        file.close();
    }

    return true;
}

// bool delete_poly(QString user, QString procedure)
// {
//     QString poly_file = get_adder_directory() + DIRSEP + procedure + DIRSEP + user + DIRSEP + ADDER_POLYNOMIAL_FILE;

// #ifndef WIN32
//     return (unlink(poly_file.c_str()) == 0);
// #else
//     return (DeleteFile((LPCWSTR)CA2T(poly_file.c_str())) == TRUE);
// #endif
// }

bool create_keypair(QString user, QString procedure, adder::PublicKey pub_key,
                    QString password)
{
    if (!create_key_directory(user, procedure)) {
        qDebug() << "Could not create keypair, so quitting";
        return false;
    }

    adder::PrivateKey priv_key = pub_key.gen_key_pair();

    if (!write_private_key(priv_key, user, procedure, password) ||
        !write_public_key(pub_key, user, procedure)) {
        return false;
    }
}

std::vector<adder::Integer> decrypt_sum(QString user, 
                                        QString procedure, 
                                        adder::Vote vote_sum,
                                        QString password)
{
    adder::PrivateKey private_key2;
    private_key2 = read_private_key2(user, procedure, password);

    std::vector<adder::Integer> sum_vec;
    sum_vec = private_key2.partial_decrypt(vote_sum);

    return sum_vec;
}

QString short_hash(adder::Vote vote)
{
    //    return vote.short_hash();
    return "";
}

bool is_valid_user(QString user)
{
    // FIXME: put something here.
//     unsigned int i;

//     /* XXX: This assumes all alphanumeric usernames. */
//     for (i = 0; i < user.size(); i++) {
//         if (!isalnum(user[i])) {
//             return false;
//         }
//     }

    return true;
}

bool is_valid_procedure(QString procedure)
{
    // FIXME: put something here.
//     if (procedure.size() != 36) {
//         return false;
//     }

//     unsigned int i;

//     for (i = 0; i < 8; i++) {
//         if (!isxdigit(procedure[i])) {
//             return false;
//         }
//     }

//     if (procedure[i] != '-') {
//         return false;
//     }

//     for (i = 9; i < 13; i++) {
//         if (!isxdigit(procedure[i])) {
//             return false;
//         }
//     }

//     if (procedure[i] != '-') {
//         return false;
//     }

//     for (i = 14; i < 18; i++) {
//         if (!isxdigit(procedure[i])) {
//             return false;
//         }
//     }
    
//     if (procedure[i] != '-') {
//         return false;
//     }

//     for (i = 19; i < 23; i++) {
//         if (!isxdigit(procedure[i])) {
//             return false;
//         }
//     }

//     if (procedure[i] != '-') {
//         return false;
//     }

//     for (i = 24; i < 36; i++) {
//         if (!isxdigit(procedure[i])) {
//             return false;
//         }
//     }

    return true;
}
