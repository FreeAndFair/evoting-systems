/* -*- Mode: C++; tab-width: 4; indent-tabs-mode: nil; c-basic-offset: 4 -*- */

#include <iostream>
#include <vector>
#include <sstream>
#include <string>

#include "time.h"

#include "common.h"
#include "Context.h"
#include "misc.h"
#include "PrivateKey.h"
#include "PublicKey.h"
#include "Integer.h"
#include "Polynomial.h"
#include "MembershipProof.h"
#include "ElgamalCiphertext.h"
#include "VoteProof.h"

using namespace adder;
using namespace std;

int main()
{
    Context ctx(true);
    PublicKey pub_key(&ctx);
    pub_key.make_partial_key(adder::Integer("51203"));

    cout << "pub_key = " << pub_key.str() << endl;

    Integer p = pub_key.get_p();
    Integer g = pub_key.get_g();
    Integer f = pub_key.get_f();

    PublicKey auth_pub_key1 = pub_key;
    PublicKey auth_pub_key2 = pub_key;

    PrivateKey auth_priv_key1 = auth_pub_key1.gen_key_pair();
    PrivateKey auth_priv_key2 = auth_pub_key2.gen_key_pair();

    cout << "auth_pub_key1 = " << auth_pub_key1.str() << endl;
    cout << "auth_pub_key2 = " << auth_pub_key2.str() << endl;
    cout << "auth_priv_key1 = " << auth_priv_key1.str() << endl;
    cout << "auth_priv_key2 = " << auth_priv_key2.str() << endl;

    Polynomial auth_poly1(&ctx, p, g, f);
    Polynomial auth_poly2(&ctx, p, g, f);

    auth_poly1.gen_rand_coeffs(1, p);
    auth_poly2.gen_rand_coeffs(1, p);

    cout << "auth_poly1 = " << auth_poly1.str() << endl;
    cout << "auth_poly2 = " << auth_poly2.str() << endl;

    ElgamalCiphertext poly1_1 = auth_pub_key1.encrypt_poly(auth_poly1.evaluate(1));
    ElgamalCiphertext poly1_2 = auth_pub_key2.encrypt_poly(auth_poly1.evaluate(2));
    ElgamalCiphertext poly2_1 = auth_pub_key1.encrypt_poly(auth_poly2.evaluate(1));
    ElgamalCiphertext poly2_2 = auth_pub_key2.encrypt_poly(auth_poly2.evaluate(2));
    
    cout << "poly1_1 = " << poly1_1.str() << endl;
    cout << "poly1_2 = " << poly1_2.str() << endl;
    cout << "poly2_1 = " << poly2_1.str() << endl;
    cout << "poly2_2 = " << poly2_2.str() << endl;
    
    vector<ElgamalCiphertext> poly_1;
    poly_1.push_back(poly1_1);
    poly_1.push_back(poly2_1);
    vector<ElgamalCiphertext> poly_2;
    poly_2.push_back(poly1_2);
    poly_2.push_back(poly2_2);
    
    PrivateKey auth_fin_priv_key1 = auth_priv_key1.get_final_priv_key(poly_1);
    PrivateKey auth_fin_priv_key2 = auth_priv_key2.get_final_priv_key(poly_2);
    
    cout << "auth_fin_priv_key1 = " << auth_fin_priv_key1.str() << endl;
    cout << "auth_fin_priv_key2 = " << auth_fin_priv_key2.str() << endl;

    Integer gvalue_1 = g.pow(auth_poly1.evaluate(0));
    Integer gvalue_2 = g.pow(auth_poly2.evaluate(0));

    cout << "gvalue_1 = " << gvalue_1 << endl;
    cout << "gvalue_2 = " << gvalue_2 << endl;

     Integer final_h = gvalue_1 * gvalue_2;

     PublicKey final_pub_key(&ctx, p, g, final_h, f);

     cout << "final_pub_key = " << final_pub_key.str() << endl;

//      int int_vote1 = rand() % choices;
//      int int_vote2 = rand() % choices;
//      int int_vote3 = rand() % choices;
//      int int_vote4 = rand() % choices;
//      int int_vote5 = rand() % choices;
//      int int_vote6 = rand() % choices;
//      int int_vote7 = rand() % choices;
//      int int_vote8 = rand() % choices;
//      int int_vote9 = rand() % choices;
//      int int_vote10 = rand() % choices;
//      int int_vote11 = rand() % choices;
//      int int_vote12 = rand() % choices;
//      int int_vote13 = rand() % choices;
//      int int_vote14 = rand() % choices;
     //     int int_vote15 = rand() % choices;
//     int int_vote16 = rand() % choices;
//     int int_vote17 = rand() % choices;
//     int int_vote18 = rand() % choices;
//     int int_vote19 = rand() % choices;
//     int int_vote20 = rand() % choices;

//     cout << int_vote1 << endl;
//     cout << int_vote2 << endl;
//     cout << int_vote3 << endl;
//     cout << int_vote4 << endl;
//     cout << int_vote5 << endl;
//     cout << int_vote6 << endl;
//     cout << int_vote7 << endl;
//     cout << int_vote8 << endl;
//     cout << int_vote9 << endl;
//     cout << int_vote10 << endl;
//     cout << int_vote11 << endl;
//     cout << int_vote12 << endl;
//     cout << int_vote13 << endl;
//     cout << int_vote14 << endl;
//     cout << int_vote15 << endl;
//     cout << int_vote16 << endl;
//     cout << int_vote17 << endl;
//     cout << int_vote18 << endl;
//     cout << int_vote19 << endl;
//     cout << int_vote20 << endl;


     std::vector<bool> vec_1;
     vec_1.push_back(true);
     vec_1.push_back(false);
     vec_1.push_back(false);
     Vote vote1 = final_pub_key.encrypt(vec_1);
     cout << "test G = " << vote1.get_cipher_vec()[2].get_G() << endl;

     std::vector<bool> vec_2;
     vec_2.push_back(false);
     vec_2.push_back(false);
     vec_2.push_back(true);
     Vote vote2 = final_pub_key.encrypt(vec_2);

//      Vote vote3 = final_pub_key.encrypt(int_vote3, base);
//      Vote vote4 = final_pub_key.encrypt(int_vote4, base);
//      Vote vote5 = final_pub_key.encrypt(int_vote5, base);
//     Vote vote6 = final_pub_key.encrypt(int_vote6, base);
//     Vote vote7 = final_pub_key.encrypt(int_vote7, base);
//     Vote vote8 = final_pub_key.encrypt(int_vote8, base);
//     Vote vote9 = final_pub_key.encrypt(int_vote9, base);
//     Vote vote10 = final_pub_key.encrypt(int_vote10, base);
//     Vote vote11 = final_pub_key.encrypt(int_vote11, base);
//     Vote vote12 = final_pub_key.encrypt(int_vote12, base);
//     Vote vote13 = final_pub_key.encrypt(int_vote13, base);
//     Vote vote14 = final_pub_key.encrypt(int_vote14, base);
//     Vote vote15 = final_pub_key.encrypt(int_vote15, base);
//     Vote vote16 = final_pub_key.encrypt(int_vote16, base);
//     Vote vote17 = final_pub_key.encrypt(int_vote17, base);
//     Vote vote18 = final_pub_key.encrypt(int_vote18, base);
//     Vote vote19 = final_pub_key.encrypt(int_vote19, base);
//     Vote vote20 = final_pub_key.encrypt(int_vote20, base);

//     cout << "vote1 = " << vote1.str() << endl;
//     cout << "vote2 = " << vote2.str() << endl;
//     cout << "vote3 = " << vote3.str() << endl;
//     cout << "vote4 = " << vote4.str() << endl;    
//     cout << "vote5 = " << vote5.str() << endl;    
//     cout << "vote6 = " << vote6.str() << endl;    
//     cout << "vote7 = " << vote7.str() << endl;    
//     cout << "vote8 = " << vote8.str() << endl;    
//     cout << "vote9 = " << vote9.str() << endl;    
//     cout << "vote10 = " << vote10.str() << endl;    
//     cout << "vote11 = " << vote11.str() << endl;    
//     cout << "vote11.hash = " << vote11.short_hash() << endl;

     adder::VoteProof proof1;
     adder::VoteProof proof2;
//     adder::BallotProof proof3(p);
//     adder::BallotProof proof4(p);
//     adder::BallotProof proof5(p);
//     adder::BallotProof proof6(p);
//     adder::BallotProof proof7(p);
//     adder::BallotProof proof8(p);
//     adder::BallotProof proof9(p);
//     adder::BallotProof proof10(p);
//     adder::BallotProof proof11(p);
//     adder::BallotProof proof12(p);
//     adder::BallotProof proof13(p);
//     adder::BallotProof proof14(p);
//     adder::BallotProof proof15(p);
//     adder::BallotProof proof16(p);
//     adder::BallotProof proof17(p);
//     adder::BallotProof proof18(p);
//     adder::BallotProof proof19(p);
//     adder::BallotProof proof20(p);

     cout << "computing proof 1 \n";
     proof1.compute(vote1, 
                    final_pub_key,
                    vec_1,
                    0, 1);
     cout << "computing proof 2 \n";
     proof2.compute(vote2,
                    final_pub_key,
                    vec_2,
                    0, 1);

//     proof3.compute(vote3, final_pub_key, int_vote3, base, choices);
//     proof4.compute(vote4, final_pub_key, int_vote4, base, choices);
//     proof5.compute(vote5, final_pub_key, int_vote5, base, choices);
//     proof6.compute(vote6, final_pub_key, int_vote6, base, choices);
//     proof7.compute(vote7, final_pub_key, int_vote7, base, choices);
//     proof8.compute(vote8, final_pub_key, int_vote8, base, choices);
//     proof9.compute(vote9, final_pub_key, int_vote9, base, choices);
//     proof10.compute(vote10, final_pub_key, int_vote10, base, choices);
//     proof11.compute(vote11, final_pub_key, int_vote11, base, choices);
//     proof12.compute(vote12, final_pub_key, int_vote12, base, choices);
//     proof13.compute(vote13, final_pub_key, int_vote13, base, choices);
//     proof14.compute(vote14, final_pub_key, int_vote14, base, choices);
//     proof15.compute(vote15, final_pub_key, int_vote15, base, choices);
//     proof16.compute(vote16, final_pub_key, int_vote16, base, choices);
//     proof17.compute(vote17, final_pub_key, int_vote17, base, choices);
//     proof18.compute(vote18, final_pub_key, int_vote18, base, choices);
//     proof19.compute(vote19, final_pub_key, int_vote19, base, choices);
//     proof20.compute(vote20, final_pub_key, int_vote20, base, choices);

     cout << "proof1 = " << proof1.str() << endl;
     cout << "proof2 = " << proof2.str() << endl;
//     cout << "proof3 = " << proof3.str() << endl;
//     cout << "proof4 = " << proof4.str() << endl;    
//     cout << "proof5 = " << proof5.str() << endl;    
//     cout << "proof6 = " << proof6.str() << endl;    
//     cout << "proof7 = " << proof7.str() << endl;    
//     cout << "proof8 = " << proof8.str() << endl;    
//     cout << "proof9 = " << proof9.str() << endl;    
//     cout << "proof10 = " << proof10.str() << endl;    
//     cout << "proof11 = " << proof11.str() << endl;    
    
//      ElgamalCiphertext c = final_pub_key.encrypt(2);
//      MembershipProof c_proof;
//      vector<Integer> dom;
//      dom.push_back(0);
//      //     dom.push_back(1);
//      dom.push_back(2);
//      c_proof.compute(c, final_pub_key, 1, dom);
//      assert(c_proof.verify(c, final_pub_key, dom));
     cout << "verifying 1\n";
     assert(proof1.verify(vote1, final_pub_key, 0, 1));
     cout << "verifying 2\n";
     assert(proof2.verify(vote2, final_pub_key, 0, 1));
//     assert(proof3.verify(vote3, final_pub_key, base, choices));
//     assert(proof4.verify(vote4, final_pub_key, base, choices));
//     assert(proof5.verify(vote5, final_pub_key, base, choices));
//     assert(proof6.verify(vote6, final_pub_key, base, choices));
//     assert(proof7.verify(vote7, final_pub_key, base, choices));
//     assert(proof8.verify(vote8, final_pub_key, base, choices));
//     assert(proof9.verify(vote9, final_pub_key, base, choices));
//     assert(proof10.verify(vote10, final_pub_key, base, choices));
//     assert(proof11.verify(vote11, final_pub_key, base, choices));
//     assert(proof12.verify(vote12, final_pub_key, base, choices));
//     assert(proof13.verify(vote13, final_pub_key, base, choices));
//     assert(proof14.verify(vote14, final_pub_key, base, choices));
//     assert(proof15.verify(vote15, final_pub_key, base, choices));
//     assert(proof16.verify(vote16, final_pub_key, base, choices));
//     assert(proof17.verify(vote17, final_pub_key, base, choices));
//     assert(proof18.verify(vote18, final_pub_key, base, choices));
//     assert(proof19.verify(vote19, final_pub_key, base, choices));
//     assert(proof20.verify(vote20, final_pub_key, base, choices));

     vector<Vote> votes;
     votes.push_back(vote1);
     votes.push_back(vote2);

     cout << "vote1 = " << vote1.str() << endl;
//     votes.push_back(vote3);
//     votes.push_back(vote4);
//     votes.push_back(vote5);
//     votes.push_back(vote6);
//     votes.push_back(vote7);
//     votes.push_back(vote8);
//     votes.push_back(vote9);
//     votes.push_back(vote10);
//     votes.push_back(vote11);
//     votes.push_back(vote12);
//     votes.push_back(vote13);
//     votes.push_back(vote14);
//     votes.push_back(vote15);
//     votes.push_back(vote16);
//     votes.push_back(vote17);
//     votes.push_back(vote18);
//     votes.push_back(vote19);
//     votes.push_back(vote20);

     Vote cipher_sum = sum_votes(votes, p);

     cout << "cipher_sum = " << cipher_sum.str() << endl;

     std::vector<Integer> partial1 = auth_fin_priv_key1.partial_decrypt(cipher_sum);
     std::vector<Integer> partial2 = auth_fin_priv_key2.partial_decrypt(cipher_sum);

     //     cout << "partial1 = " << partial1 << endl;
//     cout << "partial2 = " << partial2 << endl;

     vector< vector<Integer> > partial_sums;
     partial_sums.push_back(partial1);
     partial_sums.push_back(partial2);
     
     vector<Integer> coeffs;
     coeffs.push_back(1);
     coeffs.push_back(2);
    
     vector<Integer> result = get_final_sum(partial_sums, 
                                            coeffs, 
                                            cipher_sum, 
                                            Integer(2), 
                                            final_pub_key);
     cout << "Result\n"
          << "------\n";

     for (unsigned int i = 0; i < result.size(); i++) {
         cout << result[i] << endl;
     }
}
