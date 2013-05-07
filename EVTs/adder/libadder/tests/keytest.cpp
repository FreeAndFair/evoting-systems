/* -*- Mode: C++; tab-width: 4; indent-tabs-mode: nil; c-basic-offset: 4 -*- */

#include <iostream>
#include <vector>
#include <string>

#include "libadder.h"

using namespace std;

int main()
{
    /*    std::vector<std::string> key_pair;
    std::vector<std::string> p_g_f = adder::gen_p_g_f(40, false);

    key_pair = adder::gen_key_pair(p_g_f, 40, false);

    std::cout << "Testing: key string format generation\n";
    std::cout << "-------------------------------------\n";

    std::string test_str;
    
    //    test_str = adder::gen_pub_key_str(key_pair);
    test_str = "p23423423g23432423423h2342342342f234234234";
    
    std::cout << "key string is: " << test_str << std::endl << std::endl;

    std::cout << "Testing: key validation\n";
    std::cout << "-----------------------\n";
    
    bool test_bool = adder::is_valid_key(test_str);
    
    if (test_bool == true) {
        std::cout << "VALID KEY\n";
    } else {
        std::cout << "INVALID KEY\n";
        return 1;
    }


    std::cout << "Testing: key string parsing\n";
    std::cout << "---------------------------\n";

    std::vector<std::string> test_vect;

    try {
        test_vect = adder::parse_pub_key_str(test_str);
    } catch (std::string err) {
        std::cout << err << std::endl;
        return 1;
    }

    std::cout << "p = " << test_vect[0] << std::endl
              << "g = " << test_vect[1] << std::endl
              << "h = " << test_vect[2] << std::endl
              << "f = " << test_vect[3] << std::endl;*/

    adder::Context c(true);
    string pubkey_str("p9827942g9287692h23094782698f234234");
    cout << pubkey_str << endl;
    adder::PublicKey pk(&c);
    pk.load_from_armor(pubkey_str);
    cout << pk.str() << endl;

    std::vector<adder::Vote> key_list;

    adder::PrivateKey priv_key;
    priv_key.load_from_armor("p167g76x44f44");
    adder::Vote key1;
    key1.load_from_armor("p167G127H64");
    std::cout << "pushing " << key1.str() << std::endl;
    key_list.push_back(key1);
    adder::Vote key2;
    key2.load_from_armor("p167G12H84");
    std::cout << "pushing " << key2.str() << std::endl;
    key_list.push_back(key2);

    adder::PrivateKey final_key = priv_key.get_final_priv_key(key_list);
    std::cout << "final key is " << final_key.armor() << std::endl;

    adder::Integer p(167);
    adder::PublicKey pub_key(&c, 
                             adder::Integer(p), 
                             adder::Integer("76", p, 10), 
                             adder::Integer("75", p, 10), 
                             adder::Integer("44", p, 10));

    adder::Vote polys = pub_key.encrypt_poly(adder::Integer(38));
    std::cout << polys.armor() << std::endl;
}
