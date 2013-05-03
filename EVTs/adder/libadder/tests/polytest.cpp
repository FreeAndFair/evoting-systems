#include <iostream>
#include <string>

#include "common.h"
#include "misc.h"
#include "Polynomial.h"
#include "libadder.h"

int main()
{
//     std::cout << "Testing: polynomial evaluation\n"
//               << "------------------------------\n";
//     adder::Context c(true);
//     adder::Polynomial P(&c, "557128969667", "123123", "123123");
//     P.gen_rand_coeffs(50, "1232313123123");
//     std::cout << P.evaluate(1) << "\n";

//     std::cout << adder::Zq_sub("1", "2", "3") << "\n";

//     std::cout << adder::Zq_divide("253242078277", "286960463156", "557128969667") << "\n";

//     std::vector<unsigned long int> indices;
//     indices.push_back(1);
//     indices.push_back(2);

//     std::cout << "Lagrange coeffs:\n";
//     std::vector<std::string> lagrange_coeffs = P.lagrange(indices);
//     std::cout << "size is " << lagrange_coeffs.size() << std::endl;
//     for (unsigned int i = 0; i < lagrange_coeffs.size(); i++) {
//         std::cout << lagrange_coeffs[i] << std::endl;
//     }
    
//     adder::Polynomial Pa(&c);
//     Pa.load_from_armor("p123123123g123123123f123123 123123 123 1231 231 23123");
//     std::cout << "Polynomial is: " << Pa.armor() << std::endl;

//     std::cout << "pubkey is " << adder::Zp_pow("63478399925", "233613951699", "612656525123") << std::endl;

    adder::Context c(true);
    std::cout << "Final test\n";
    adder::PublicKey pub_key(&c);
    pub_key.make_partial_key(40);
    adder::PrivateKey priv_key = pub_key.gen_key_pair();
    std::cout << "pub key: " << pub_key.armor() << std::endl;
    std::cout << "priv key: " << priv_key.armor() << std::endl;

    adder::Polynomial poly(&c, pub_key.get_p(), pub_key.get_g(), 
                           pub_key.get_f());
    poly.gen_rand_coeffs(0, pub_key.get_p());

    std::cout << "poly: " << poly.armor() << std::endl;
    adder::Vote e = pub_key.encrypt_poly(poly.evaluate(4));
    std::cout << "encryption: " << e.armor() << std::endl;
    std::vector<adder::Vote> es;
    es.push_back(e);
    adder::PrivateKey final = priv_key.get_final_priv_key(es);
    std::cout << "final: " << final.armor() << std::endl;
    
    return 0;
}
