/* -*- Mode: C++; tab-width: 4; indent-tabs-mode: nil; c-basic-offset: 4 -*- */

#include <iostream>
#include <string>

#include "common.h"
#include <assert.h>
#include "Context.h"
#include "Integer.h"
#include "misc.h"
#include "PrivateKey.h"
#include "PublicKey.h"
#include "Vote.h"
#include "BallotProof.h"

int main()
{
    adder::Context context(true);
    adder::PublicKey pub_key(&context);
    adder::PrivateKey priv_key;

    pub_key.make_partial_key(40);
    priv_key = pub_key.gen_key_pair();

    //    pub_key.load_from_armor("p722059515323g690047919613h4294967295f313622213037");

    std::cout << "pub_key = " << pub_key.str() << std::endl;
    std::cout << "priv_key = " << priv_key.str() << std::endl;

    adder::Integer p(pub_key.get_p());

    adder::Integer q((p - 1) / 2);
    adder::Integer g(pub_key.get_g());
    adder::Integer h(pub_key.get_h());
    adder::Integer f(pub_key.get_f());
    adder::Vote vote;
    
    std::cout << "g.m = " << g.get_modulus() << std::endl
              << "h.m = " << h.get_modulus() << std::endl
              << "f.m = " << f.get_modulus() << std::endl;

    adder::Integer base("3", q, 10);
    vote = pub_key.encrypt(1, base);

    std::cout << "vote = " << vote.str() << std::endl;

    adder::BallotProof proof(p);
    proof.compute(vote, pub_key, 1, base, 3);

    std::cout << "proof = " << proof.str() << std::endl;

    assert(proof.verify(vote, pub_key, base, 3));

    std::string proof_str("y123y234y345z0987z987z987s111s222s333s444s555c7654c7654c7654");
    adder::BallotProof bp(p);
    bp.load_from_armor(proof_str);

    std::cout << bp.str() << std::endl;
        
    return 0;
}
