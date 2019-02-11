/****************************************************************
 * test coefficients
 ****************************************************************/

#define COEFF_IS_pADIC

#if 0
#define MODULUS_PRIME 18446744073709551557ULL
#elif 0
#define MODULUS_PRIME 4294967291ULL
#elif 0
#define MODULUS_PRIME 5
#elif 1
#define MODULUS_PRIME 3
#elif 0
#define MODULUS_PRIME 2
#endif

#define MODULUS_EXPONENT 100

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include "coeff.h"

uint64_t rand64(void) {
  uint64_t n = 0;
  for (unsigned i = 0; i < 5; i++)
    n = (n << 13) | rand();
  return n;
}

int main(int argc, char *argv[]) {
  printf("ID: %s\n", COEFF_ID);

  coeff data[100];

  for (long i = 0; i < 25; i++)
    coeff_set_si(data[i], 12-i);
  for (unsigned i = 25; i < 50; i++)
    coeff_set_si(data[i], rand64());
  for (unsigned i = 50; i < 100; i++)
    coeff_fdiv_q(data[i], data[i-50], data[14]);

  printf("TESTING INITIAL DATA\n");
  for (long i = 0; i < 25; i++) {
    printf("%ld,", i);
    assert(coeff_get_si(data[i]) == 12-i);
  }
  
  printf("\nTESTING SUM\n");
  for (unsigned i = 0; i < 100; i++)
    for (unsigned j = 0; j < 100; j++) {
      printf("(%d,%d),", i, j);
      coeff s, t;
      coeff_add(s, data[i], data[j]);
      coeff_add(t, data[j], data[i]);
      assert(!coeff_cmp(s, t));
      coeff_sub(s, s, data[i]);
      assert(!coeff_cmp(s, data[j]));
      coeff_sub(t, t, data[i]);
      assert(!coeff_cmp(s, data[j]));
    }      

  printf("\nTESTING GCD\n");
  for (unsigned i = 0; i < 100; i++)
    for (unsigned j = 0; j < 100; j++) {
      printf("(%d,%d),", i, j);
      coeff g, s, t, u, a;
      if (coeff_z_p(data[j]))
	continue;
      coeff_gcdext(g, s, t, data[i], data[j]);

      coeff_mul(u, t, data[j]);

      printf("%d %d: %ld = %ld*%ld + %ld*%ld; %ld\n", i, j, coeff_get_si(g), coeff_get_si(s), coeff_get_si(data[i]), coeff_get_si(t), coeff_get_si(data[j]), coeff_get_si(u) );

      coeff_unit_annihilator(u, a, g);
      assert(!coeff_cmp_si(u, 1));
      coeff_mul(a, a, g);
      assert(coeff_z_p(a));
      coeff_submul(g, s, data[i]);
      coeff_submul(g, t, data[j]);
      assert(coeff_z_p(g));
    }
    
  return 0;
}
