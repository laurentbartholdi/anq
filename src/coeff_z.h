/******************************************************************************
**
**               Nilpotent Quotient for Lie Algebras
** coeff_z.h
** defines coefficients as arbitrary-precision integers, with fast code for
** integers fitting in 63 bits
*/

#error broken

#include "z.h"
typedef z_t coeff;

/* addition */
inline bool coeff_nz(const coeff a) {
  return mpz_sgn(a) != 0;
}

#define coeff_init z_init
#define coeff_init_set z_init_set
#define coeff_init_set_si z_init_set_si
#define coeff_get_si z_get_si
#define coeff_set z_set
#define coeff_set_si z_set_si
#define coeff_clear z_clear

#define coeff_add z_add
#define coeff_addmul z_addmul
#define coeff_cmp z_cmp
#define coeff_cmp_si z_cmp_si
#define coeff_divexact z_divexact
#define coeff_fdiv_q z_fdiv_q
#define coeff_gcdext z_gcdext
#define coeff_mul z_mul
#define coeff_neg z_neg
#define coeff_sgn z_sgn
#define coeff_sub z_sub
#define coeff_submul z_submul

/* addition, unused */
inline void coeff_swap(coeff &a, coeff &b) {
  coeff t;
  z_init_set(t, a);
  z_set(a, b);
  z_set(b, t);
  z_clear(t);
}
