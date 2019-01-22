/******************************************************************************
**
**               Nilpotent Quotient for Lie Algebras
** coeff_2_k.h
** defines coefficients as residues modulo 2^k
*/

#include <inttypes.h>

#if MODULUS_EXPONENT > 64
#error MODULUS_EXPONENT must be <= 64; for larger exponent, use coeff_2_mp.h
#include </> // abort
#endif

#define __COEFF_ID(x) #x
#define _COEFF_ID(x) "Z/2^" __COEFF_ID(x) " as uint64_t"
#define COEFF_ID _COEFF_ID(MODULUS_EXPONENT)
#if MODULUS_EXPONENT == 64
#define COEFF_MASK ((uint64_t) ~0LL)
#else
#define COEFF_MASK ((1ULL << MODULUS_EXPONENT) - 1)
#endif

struct coeff {
  uint64_t data;
};

/* addition */
inline bool coeff_nz_p(const coeff &a) {
  return a.data != 0;
}

inline bool coeff_z_p(const coeff &a) {
  return a.data == 0;
}

inline void coeff_init(coeff &a) {
}

inline void coeff_init_set(coeff &result, const coeff &a) {
  result.data = a.data;
}

inline void coeff_init_set_si(coeff &result, const long a) {
  result.data = a & COEFF_MASK;
}

inline void coeff_set(coeff &result, const coeff &a) {
  coeff_init_set(result, a);
}

inline void coeff_set_si(coeff &result, const long a) {
  coeff_init_set_si(result, a);
}

/* addition */
inline void coeff_zero(coeff &result) {
  coeff_set_si(result, 0);
}

inline long coeff_get_si(const coeff &a) {
  return a.data;
}

inline void coeff_clear(coeff &a) {
}

inline void coeff_add(coeff &result, const coeff &a, const coeff &b) {
  result.data = (a.data + b.data) & COEFF_MASK;
}

inline void coeff_add_si(coeff &result, const coeff &a, long b) {
  result.data = (a.data + b) & COEFF_MASK;
}
inline void coeff_addmul(coeff &result, const coeff &a, const coeff &b) {
  result.data = (result.data + a.data * b.data ) & COEFF_MASK;
}

inline int coeff_cmp(const coeff &a, const coeff &b) {
  return (a.data > b.data) - (a.data < b.data);
}

/* I don't know how to implement a meaningful compare on residue classes. Let's return 0 or 1 */
inline int coeff_cmp_si(const coeff &a, long b) {
  return a.data != (unsigned long) (b & COEFF_MASK);
}

inline void coeff_divexact(coeff &result, const coeff &a, const coeff &b) {
  result.data = a.data / b.data;
}

inline void coeff_fdiv_q(coeff &result, const coeff &a, const coeff &b) {
  result.data = a.data / b.data;
}

inline void coeff_fdiv_r(coeff &result, const coeff &a, const coeff &b) {
  result.data = a.data % b.data;
}

inline void coeff_mul(coeff &result, const coeff &a, const coeff &b) {
  result.data = (a.data * b.data) & COEFF_MASK;
}

inline void coeff_mul_si(coeff &result, const coeff &a, long b) {
  result.data = (a.data * b) & COEFF_MASK;
}

inline void coeff_neg(coeff &result, const coeff &a) {
  result.data = (-a.data) & COEFF_MASK;
}

/* unused */
inline int coeff_sgn(const coeff &a) {
  return a.data != 0;
}

inline void coeff_sub(coeff &result, const coeff &a, const coeff &b) {
  result.data = (a.data - b.data) & COEFF_MASK;
}

inline void coeff_submul(coeff &result, const coeff &a, const coeff &b) {
  result.data = (result.data - a.data * b.data) & COEFF_MASK;
}

/* addition, unused */
inline void coeff_swap(coeff &a, coeff &b, coeff &tmp) {
  coeff_set(tmp, a);
  coeff_set(a, b);
  coeff_set(b, tmp);
}

inline coeff inverse_mod_2_k(uint64_t a, unsigned shift) {
  a >>= shift;
  unsigned long inverse = a; // already 3 correct bits
  for (unsigned i = 0; i < 5; i++)
    inverse *= 2 - a*inverse;

  return { .data = inverse & COEFF_MASK };
}

inline void coeff_inv(coeff &result, const coeff &a) {
  if (a.data & 1)
    result = inverse_mod_2_k(a.data, 0);
  else
    coeff_set_si(result, 0);
}

inline void coeff_gcdext(coeff &gcd, coeff &s, coeff &t, const coeff &a, const coeff &b) {
  unsigned long aval = a.data & -a.data, bval = b.data & -b.data;
  if (a.data == 0 || aval >= bval) {
    gcd.data = bval;
    s.data = 0;
    t = inverse_mod_2_k(b.data, __builtin_ctzl(bval)); // b.data / bval
  } else {
    gcd.data = aval;
    s = inverse_mod_2_k(a.data, __builtin_ctzl(aval));
    t.data = 0;
  }
}

/* addition, returns true if a in [0,b) or b=0 */
inline bool coeff_reduced_p(const coeff &a, const coeff &b) {
  return b.data == 0 || a.data < b.data;
}

/* addition, returns unit and generator of annihilator ideal:
   a*unit is canonical (2^n) and a*annihilator=0 */
inline void coeff_unit_annihilator(coeff &unit, coeff &annihilator, const coeff &a) {
  if (a.data == 0) {
    unit.data = 0;
    annihilator.data = 1;
    return;
  }
  int shift = __builtin_ctzl(a.data);
  unit = inverse_mod_2_k(a.data, shift);
  if (shift == 0)
    annihilator.data = 0;
  else
  annihilator.data = 1ULL << (MODULUS_EXPONENT-shift);
}

inline int coeff_out_str(FILE *f, const coeff &a)
{
  return fprintf(f, "%lu", (unsigned long) a.data); /* maybe we should print in binary or hex? */
}

#define coeff_base 2
