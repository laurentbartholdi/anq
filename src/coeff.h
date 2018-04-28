/******************************************************************************
**
**               Nilpotent Quotient for Lie Algebras
** coeff.h
** generic interface to coefficients
*/

/****************************************************************
 * coefficients can be of various types, with varying performance:
 * - signed long int
 * - multiprecision gmpz_t
 * - hybrid 63-bit signed long / gmpz_t
 * - mod-2^k arithmetic (unsigned long int or gmpn_t)
 * - mod-p^k arithmetic (unsigned long int or gmpn_t)
 ****************************************************************/
#ifdef COEFF_IS_LONG
#  include "coeff_long.h"
#elif defined(COEFF_IS_MPZ)
#  include "coeff_mpz.h"
#elif defined(COEFF_IS_Z)
#  include "coeff_z.h"
#elif defined(COEFF_IS_pADIC)
#  if MODULUS_PRIME == 2
#    define MODULUS_MAXEXPONENT 64
#  elif MODULUS_PRIME == 3
#    define MODULUS_MAXEXPONENT 40
#  elif MODULUS_PRIME == 5
#    define MODULUS_MAXEXPONENT 27
#  elif MODULUS_PRIME == 7
#    define MODULUS_MAXEXPONENT 22
#  elif MODULUS_PRIME == 11
#    define MODULUS_MAXEXPONENT 18
#  elif MODULUS_PRIME == 13
#    define MODULUS_MAXEXPONENT 17
#  elif MODULUS_PRIME <= 19
#    define MODULUS_MAXEXPONENT 15
#  elif MODULUS_PRIME <= 23
#    define MODULUS_MAXEXPONENT 14
#  elif MODULUS_PRIME == 29
#    define MODULUS_MAXEXPONENT 13
#  elif MODULUS_PRIME <= 37
#    define MODULUS_MAXEXPONENT 12
#  elif MODULUS_PRIME <= 53
#    define MODULUS_MAXEXPONENT 11
#  elif MODULUS_PRIME <= 83
#    define MODULUS_MAXEXPONENT 10
#  elif MODULUS_PRIME <= 137
#    define MODULUS_MAXEXPONENT 9
#  elif MODULUS_PRIME <= 251
#    define MODULUS_MAXEXPONENT 8
#  elif MODULUS_PRIME <= 563
#    define MODULUS_MAXEXPONENT 7
#  elif MODULUS_PRIME <= 1621
#    define MODULUS_MAXEXPONENT 6
#  elif MODULUS_PRIME <= 7129
#    define MODULUS_MAXEXPONENT 5
#  elif MODULUS_PRIME <= 65521
#    define MODULUS_MAXEXPONENT 4
#  elif MODULUS_PRIME <= 264221
#    define MODULUS_MAXEXPONENT 3
#  elif MODULUS_PRIME <= 4294967291
#    define MODULUS_MAXEXPONENT 2
#  else
#    define MODULUS_MAXEXPONENT 1
#  endif
#  ifndef MODULUS_EXPONENT
#    define MODULUS_EXPONENT MODULUS_MAXEXPONENT
#  endif
#  if MODULUS_EXPONENT <= MODULUS_MAXEXPONENT
#    if MODULUS_PRIME == 2
#      include "coeff_2_k.h"
#    else
#      include "coeff_p_k.h"
#    endif
#  else
#    if MODULUS_PRIME == 2
#      include "coeff_2_mp.h"
#    else
#      include "coeff_p_mp.h"
#    endif
#  endif
#else
#  error you must specify a coefficient type: COEFF_IS_LONG, ...
#  include </> // force stop
#endif

/* generic routines */
inline void coeff_pow(coeff &result, const coeff &a, const coeff &b) {
  /* kludge: coerce b to an integer */
  int exp = coeff_get_si (b);
  coeff r, base;
  coeff_init_set_si (r, 1);
  coeff_init_set (base, a);
  while (exp) {
    if (exp & 1)
      coeff_mul(r, r, base);
    exp >>= 1;
    coeff_mul(base, base, base);
  }
  coeff_set(result, r);
  coeff_clear(r);
  coeff_clear(base);
}

#ifndef coeff_base
#define coeff_base 10
#endif
