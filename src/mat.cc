// test for rref

#include "rref.h"

const uint64_t MODULUS_PRIME = 3;
const uint64_t MODULUS_EXPONENT = 4;

int main(int argc, char *argv[]) {
  sparse_mat<long> a;
  int prime = 2;
  // a(0,1) = 2; a(1,2) = 8; a(2,4) = 16; a(3,0) = 4;
  //a(4,6) = 1; a(4,0) = 2; a(0,1) = 8; a(2,4) = 16; a(3,0) = 4;
  a(0,5) = 2;
  a(0,4) = 3;
  a(0,3) = 1;
  a(0,2) = 7;
  a(1,3) = 2;
  a(1,2) = 21;
  a(1,1) = 5;
  a.setsize();
  
  std::cout << a;

  auto p = a.nullspace();

  std::cout << p << std::endl;
}
