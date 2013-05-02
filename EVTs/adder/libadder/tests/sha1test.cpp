#include <iostream>
#include <string>

#include "libadder.h"

int main()
{
    std::string empty = "";
    std::string emptydigest = "da39a3ee5e6b4b0d3255bfef95601890afd80709";
    std::string hello = "hello";
    std::string hellodigest = "aaf4c61ddcc5e8a2dabede0f3b482cd9aea9434d";
    std::string adder_emptydigest = adder::sha1(empty);
    std::string adder_hellodigest = adder::sha1(hello); 
    
    std::cout << emptydigest << std::endl << adder_emptydigest << std::endl;
    assert(emptydigest == adder_emptydigest);
    std::cout << hellodigest << " " << adder_hellodigest << std::endl;
    assert(hellodigest == adder_hellodigest);

    return 0;
}
