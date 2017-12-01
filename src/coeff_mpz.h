/******************************************************************************
**
**               Nilpotent Quotient for Lie Algebras
** coeff_mpz.h
** defines coefficients as arbitrary-precision integers
*/

#error broken

#include<gmp.h>
typedef mpz_t coeff;

/* addition */
inline bool coeff_nz(const coeff a) {
  return mpz_sgn(a) != 0;
}

#define coeff_init mpz_init
#define coeff_init_set mpz_init_set
#define coeff_init_set_si mpz_init_set_si
#define coeff_get_si mpz_get_si
#define coeff_set mpz_set
#define coeff_set_si mpz_set_si
#define coeff_clear mpz_clear

#define coeff_add mpz_add
#define coeff_addmul mpz_addmul
#define coeff_cmp mpz_cmp
#define coeff_cmp_si mpz_cmp_si
#define coeff_divexact mpz_divexact
#define coeff_fdiv_q mpz_fdiv_q
#define coeff_fdiv_q mpz_fdiv_r
#define coeff_gcdext mpz_gcdext
#define coeff_mul mpz_mul
#define coeff_neg mpz_neg
#define coeff_sgn mpz_sgn
#define coeff_sub mpz_sub
#define coeff_submul mpz_submul

/* addition, unused */
inline void coeff_swap(coeff &a, coeff &b) {
  coeff t;
  mpz_init_set(t, a);
  mpz_set(a, b);
  mpz_set(b, t);
  mpz_clear(t);
}
