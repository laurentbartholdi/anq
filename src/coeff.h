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
 * - mod-2^64 arithmetic (unsigned long int)
 * - mod-p^k arithmetic (unsigned long int)
 ****************************************************************/
#ifdef COEFF_IS_LONG
#include "coeff_long.h"
#elif defined(COEFF_IS_MPZ)
#include "coeff_mpz.h"
#elif defined(COEFF_IS_Z)
#include "coeff_z.h"
#elif defined(COEFF_IS_MOD2_64)
#include "coeff_2_64.h"
#elif defined(COEFF_IS_MODp_k)
#include "coeff_p_k.h"
#else
#error you must specify a coefficient type: COEFF_IS_LONG, ...
#include </> // force stop
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
