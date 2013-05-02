/* -*- Mode: C++; tab-width: 4; indent-tabs-mode: nil; c-basic-offset: 4 -*- */

#include <iostream>
#include <vector>
#include <string>

#include "libadder.h"

int main()
{
    std::string message;
    std::string enc_msg;
    std::string dec_msg;
    std::string arm_msg;
    std::string drm_msg;
    std::string test_str;

    message = "It's not your blue blood, your pedigree or your college degree. It's what you do with your life that counts.\n\004";
    
    std::cout << std::endl << std::endl;
    
    std::cout << "Testing: message\n";
    std::cout << "--------------------------\n";

    std::cout << "message is:\n" << message << std::endl << std::endl;

    std::cout << "Testing: radix encoding\n";
    std::cout << "-----------------------\n";
 
    enc_msg = adder::encode_radix_64(message);

        
    std::cout << "encoded string is:\n" << enc_msg  << std::endl << std::endl;

    std::cout << "Testing: armoring\n";
    std::cout << "-----------------\n";

    arm_msg = adder::en_armor(enc_msg, "TESTING");
    
    std::cout << "armored string is:\n" << arm_msg << std::endl << std::endl;

    std::cout << "Testing: dearmoring\n";
    std::cout << "-------------------\n";
    
    try { 
        drm_msg = adder::de_armor(arm_msg, "TESTING");
     } catch (char* err) {
        std::cout << err << std::endl;
        return 1;
    }
     
    std::cout << "dearmored string is:\n" << drm_msg << std::endl << std::endl;

    std::cout << "Testing: radix decoding\n";
    std::cout << "-----------------------\n";
    
    try {
        dec_msg = adder::decode_radix_64(enc_msg);
    } catch (std::string err) {
        std::cout << "Error! " << err << std::endl;
        std::cout.flush();
        return 1;
    } catch (...) {
        std::cout << "Unknown exception!\n";
        std::cout.flush();
    }

    std::cout << "decoded string is:\n" << dec_msg << std::endl << std::endl;

    std::string messge("-----BEGIN ADDER PUBLIC KEY-----\n");
    messge += " Version: Adder 0.1.0\n\n";
    messge += "cDk2MzkwNjIwMzU2N2c0NzgwMzExMTk1NTVoMGY5MzM4NjI2MTQ5Mzk=\n";
    messge += "=d9BH\n";
    messge += "-----END ADDER PUBLIC KEY-----\n";

    std::cout << messge;
    std::string decoded = adder::de_armor(messge, "PUBLIC KEY");
    decoded = adder::decode_radix_64(decoded);
    std::cout << decoded;

    return 0;
}
