/****************************************************************
 * z.c
 * fast integers, combining signed long int and gmp ints
 * (C) 2017 Laurent Bartholdi
 ****************************************************************
 * those routines that are not implemented inline.
 ****************************************************************/

#include "z.h"

void __z_add(z_t &result, const z_t &a, const z_t &b) {
  /* ideally, test if a is D, (b is P and 2b fits in long) and a+2b is OK;
     and if (a is P and 2a fits in long) and b is D and 2a+b is OK */
  if (result.t)
    result.p = new mpz_t;
  if (a.t & b.t)
    mpz_set_si(result.p, (a.d >> 1) + (b.d >> 1));
  else {
    if (a.t && a.d >= 0) mpz_add_ui(result.p, b.p, a.d >> 1);
    else if (a.t && a.d < 0) mpz_sub_ui(result.p, b.p, -a.d >> 1);
    else if (b.t && b.d >= 0) mpz_add_ui(result.p, a.p, b.d >> 1);
    else if (b.t && b.d < 0) mpz_sub_ui(result.p, a.p, -b.d >> 1);
    else mpz_add(result.p, a.p, b.p);
  }
}

void __z_mul(z_t &result, const z_t &a, const z_t &b) {
  if (result.t)
    result.p = new mpz_t;
  if (a.t && b.t)
    mpz_set_si(result.p, a.d >> 1), mpz_mul_si(result.p, result.p, b.d >> 1);
  else {
    if (a.t) mpz_mul_si(result.p, b.p, a.d >> 1);
    else if (b.t) mpz_mul_si(result.p, a.p, b.d >> 1);
    else mpz_mul(result.p, a.p, b.p);
  }
}
