/* -*- Mode: C++; tab-width: 4; indent-tabs-mode: nil; c-basic-offset: 4 -*- */

#include <iostream>
#include <string>

#include "common.h"
#include "Context.h"
#include "Integer.h"
#include "misc.h"
#include "PrivateKey.h"
#include "PublicKey.h"
#include "Vote.h"

int main()
{
    adder::Integer p(7);
    adder::Integer p_minus_1;
    adder::Integer p_minus_1_over_2;
    adder::Integer q;
    adder::Integer r(10, 3);

    std::string myVote = "0";
    adder::Vote vote;

    adder::Context context(true);
    adder::PublicKey pub_key(&context);
    adder::PrivateKey priv_key;

    pub_key.make_partial_key(56);
    priv_key = pub_key.gen_key_pair();

    p_minus_1 = p - 1;

    assert(p - 1 == 6);

    p_minus_1_over_2 = (p - 1) / 2;

    assert((p - 1) / 2 == 3);

    assert((adder::Integer(3).pow(2)) == 9);

    assert(adder::Integer(2) * 3 * 5 == 30);

    assert(adder::Integer::random(10) < 10 && adder::Integer::random(10) >= 0);

    assert(r == 1);
    assert(r * 2 == 2);

    return 0;
}
