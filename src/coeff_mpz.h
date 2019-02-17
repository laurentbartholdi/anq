/******************************************************************************
**
**               Nilpotent Quotient for Lie Algebras
** coeff_mpz.h
** defines coefficients as arbitrary-precision integers
*/

#define COEFF_ID "Z as mpz_t"

#include<gmp.h>
typedef mpz_t coeff;

/* addition */
inline bool coeff_nz_p(const coeff a) {
  return mpz_sgn(a) != 0;
}

inline bool coeff_z_p(const coeff a) {
  return mpz_sgn(a) == 0;
}

#define coeff_init mpz_init
#define coeff_init_set mpz_init_set
#define coeff_init_set_si mpz_init_set_si
#define coeff_get_si mpz_get_si
#define coeff_set mpz_set
#define coeff_set_si mpz_set_si
#define coeff_get_str mpz_get_str
#define coeff_set_str mpz_set_str
#define coeff_clear mpz_clear

/* addition */
inline void coeff_zero(coeff &result) {
  coeff_set_si(result, 0);
}

#define coeff_add mpz_add
inline void coeff_add_si(coeff &result, coeff &a, long l) {
  if (l >= 0) mpz_add_ui(result, a, l); else mpz_sub_ui(result, a, -l);
}
#define coeff_addmul mpz_addmul
#define coeff_cmp mpz_cmp
#define coeff_cmp_si mpz_cmp_si
#define coeff_divexact mpz_divexact
#define coeff_fdiv_q mpz_fdiv_q
#define coeff_fdiv_r mpz_fdiv_r
#define coeff_fdiv_qr mpz_fdiv_qr
#define coeff_gcdext mpz_gcdext
#define coeff_mul mpz_mul
#define coeff_mul_si mpz_mul_si
#define coeff_neg mpz_neg
#define coeff_sgn mpz_sgn
#define coeff_sub mpz_sub
#define coeff_submul mpz_submul

/* addition, invert number (or set to 0 if impossible) */
inline void coeff_inv(coeff &result, const coeff &a) {
  if (!coeff_cmp_si(a, 1))
    coeff_set_si(result, 1);
  else if (!coeff_cmp_si(a, -1))
    coeff_set_si(result, -1);
  else
    coeff_set_si(result, 0);
}

/* addition, returns true if a in [0,b) or b=0 */
inline bool coeff_reduced_p(coeff &a, coeff &b) {
  return !mpz_sgn(b) || (mpz_sgn(a) >= 0 && mpz_cmp(a, b) < 0);
}

/* addition, returns unit and generator of annihilator ideal:
   a*unit is canonical (2^n) and a*annihilator=0 */
inline void coeff_unit_annihilator(coeff &unit, coeff &annihilator, const coeff &a) {
  mpz_set_si(unit, mpz_sgn(a));
  mpz_set_si(annihilator, 0);
}

/* addition, unused */
inline void coeff_swap(coeff &a, coeff &b) {
  coeff t;
  mpz_init_set(t, a);
  mpz_set(a, b);
  mpz_set(b, t);
  mpz_clear(t);
}

inline int coeff_out_str(FILE *f, const coeff &a)
{
  return mpz_out_str(f, 10, a);
}
