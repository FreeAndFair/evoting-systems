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

#ifndef __KEY_MANAGEMENT_H__
#define __KEY_MANAGEMENT_H__

#include <QtCore>
#include <string>

#include "Context.h"
#include "PublicKey.h"
#include "Vote.h"
#include "Polynomial.h"

QString default_adder_directory();
adder::Vote encrypt_vote(adder::PublicKey key, int vote, int base);
bool create_directory(QString directory);
QString get_adder_key_directory(QString user, QString procedure);

adder::PublicKey read_public_key(QString user, QString proc, adder::Context* context = NULL);
bool write_public_key(adder::PublicKey key, QString user, QString proc);

adder::Polynomial read_polynomial(QString user, QString proc);
bool write_polynomial(adder::Polynomial key, QString user, QString proc);

adder::PrivateKey read_private_key(QString user, QString proc, QString password);
bool write_private_key(adder::PrivateKey key, QString user, QString proc, 
                       QString password);

adder::PrivateKey read_private_key2(QString user, QString proc, QString password);
bool write_private_key2(adder::PrivateKey key, QString user, QString proc,
                        QString password);

bool delete_poly(QString user, QString procedure);
bool create_key_directory(QString user, QString procedure);
bool create_keypair(QString user, QString procedure, adder::PublicKey pub_key,
                    QString password);
std::vector<adder::Integer> decrypt_sum(QString user, QString procedure, adder::Vote vote_sum, 
                                        QString password);
QString short_hash(adder::Vote vote);
bool is_valid_user(QString user);
bool is_valid_procedure(QString procedure);

struct Failed {};

#endif
