/* -*- Mode: C++; tab-width: 4; indent-tabs-mode: nil; c-basic-offset: 4 -*- */

#include <iostream>
#include <vector>
#include <sstream>
#include <string>

#include "time.h"
#include <sys/time.h>

#include "common.h"
#include "Context.h"
#include "misc.h"
#include "PrivateKey.h"
#include "PublicKey.h"
#include "Integer.h"
#include "Polynomial.h"
#include "BallotProof.h"

using namespace adder;
using namespace std;

int main(int argc, char** argv)
{    
//     Integer p("138801000772121024230464784458809940640188665800507185965405552475555713754608314410025942585348416229998039355503502748241953775388915297912142895694382614085265315933610703135456309422542254788701571542503365616257976988130582940615508348415009111363742340433869524561972086527125690397341662823107765223627");

//     Integer g("13517780315828887107707996414886877476707634264238258239117074438359642546692088436263043470991898686232575681298497150505808510585804570512076383679438457454312065634334090866294874652914440794941381960876702471062552013094904565886111599806172959857052677902453717608315355956176630266634319122814894443097", p);

//     Integer h("0", p);

//     Integer f("115669658323009248768005562012122638864236436078650569165314108530205785717327472486591078621663656195226787895023081026399130843951310999195459316858291812414407772695363377798935379020016111177007331779952215971792046859810705054714787141301209677551448734433000019980458844609345827913066357808527460088550", p);

    for (int i = 16; i < 1025; i += 50) {
        double total = 0;
        for (int j = 0; j < 3; j++) {
            struct itimerval value;
            value.it_interval.tv_sec = 1000000;
            value.it_interval.tv_usec = 99999;
            value.it_value.tv_sec = 1000000;
            value.it_value.tv_usec = 0;
            
            setitimer(ITIMER_VIRTUAL, &value, 0);
            
            struct itimerval o_value;
            Integer s = Integer::gen_safe_prime(i);
            
            getitimer(ITIMER_VIRTUAL, &value);
            
            total += (1000000000 - ((value.it_value.tv_sec * 1000) + 
                                    ((value.it_value.tv_usec) / 1000))) / 1000.0 ;
        }

        cout << i 
             << " " 
             << total / 3.0
             << endl;
    }
    
    //     //cout << "pub_key = " << pub_key.str() << endl;
    
//     //Integer p = pub_key.get_p();
//     //Integer g = pub_key.get_g();
//     //Integer f = pub_key.get_f();


//     Integer num_voters(argv[1]);
//     Integer num_auths(argv[2]);

//     //cout << "voters: " << num_voters << endl;
//     //cout << "auths: " << num_auths << endl;

//     PublicKey pub_key(&ctx, p, g, h, f);

//     //cout << "public key: " << pub_key.str() << endl;

//     int choices = 3;
//     Integer base = gen_base(num_voters + 1, p, choices);
//     //cout << "base: " << base << endl;
    
//     vector<PublicKey> auth_pub_keys;
//     for (int i = 0; i < num_auths; i++) {
//         auth_pub_keys.push_back(pub_key);
//     }

//     vector<PrivateKey> auth_priv_keys;
//     for (int i = 0; i < num_auths; i++) {
//         auth_priv_keys.push_back(auth_pub_keys[i].gen_key_pair());
//     }

//     for (int i = 0; i < num_auths; i++) {
//         //cout << "new public key: " << auth_pub_keys[i].str() << endl;
//         //cout << "new private key: " << auth_priv_keys[i].str() << endl;
//     }

//     vector<Polynomial> auth_polys;
//     for (int i = 0; i < num_auths; i++) {
//         auth_polys.push_back(Polynomial(&ctx, p, g, f));
//         auth_polys[i].gen_rand_coeffs(num_auths-1, p);
//         //cout << "genned poly: " << auth_polys[i].str() << endl;
//     }

//     vector< vector<Vote> > cipher_polys;
//     for (int i = 0; i < num_auths; i++) {
//         vector<Vote> vec;
//         for (int j = 0; j < num_auths; j++) {
//             vec.push_back(auth_pub_keys[i].encrypt_poly(auth_polys[j].evaluate(i+1)));
//         }
//         cipher_polys.push_back(vec);
//     }

//     vector<PrivateKey> auth_fin_priv_keys;
//     for (int i = 0; i < num_auths; i++) {
//         auth_fin_priv_keys.push_back(auth_priv_keys[i].get_final_priv_key(cipher_polys[i]));
//         //cout << "final privkey: " << auth_fin_priv_keys[i].str() << endl;
//     }

//     vector<Integer> gvalues;
//     for (int i = 0; i < num_auths; i++) {
//         gvalues.push_back(g.pow(auth_polys[i].evaluate(0)));
//     }
//     Integer final_h("1", p);
//     for (int i = 0; i < num_auths; i++) {
//         final_h = final_h * gvalues[i];
//     }

//     PublicKey final_pub_key(&ctx, p, g, final_h, f);

//     vector<Vote> votes;
//     for (int i = 0; i < num_voters; i++) {
//         Integer choice = Integer::random(choices);
//         //cout << "choice: " << choice << endl;
//         votes.push_back(final_pub_key.encrypt(choice, base));
//     }

//     Vote cipher_sum = sum_votes(votes, p);

//     vector<Integer> partial_sums;
//     for (int i = 0; i < num_auths; i++) {
//         partial_sums.push_back(auth_fin_priv_keys[i].partial_decrypt(cipher_sum));
//     }

//     vector<Integer> coeffs;
//     for (int i = 0; i < num_auths; i++) {
//         //cout << "adding coeff: " << i+1 << endl;
//         coeffs.push_back(i+1);
//     }

//     vector<Integer> result = get_final_sum(partial_sums, coeffs, cipher_sum, votes.size(), choices, base, final_pub_key);
//     for (int i = 0; i < result.size(); i++) {
//         cout << result[i] << endl;
//     }
}
