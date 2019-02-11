/******************************************************************************
**
**               Nilpotent Quotient for Lie Algebras
** coeff_2_mp.h
** defines coefficients as residues modulo 2^(64*N) with N mpn words
*/

#include <gmp.h>
#include <ctype.h>

#ifndef MODULUS_EXPONENT
#error You must specify MODULUS_EXPONENT
#include </> // abort
#endif

#define __COEFF_WORDS (MODULUS_EXPONENT + GMP_LIMB_BITS - 1)/GMP_LIMB_BITS
#if __COEFF_WORDS == 1 // pretty-print, evaluate to constant
#define COEFF_WORDS 1
#elif __COEFF_WORDS == 2
#define COEFF_WORDS 2
#elif __COEFF_WORDS == 3
#define COEFF_WORDS 3
#elif __COEFF_WORDS == 4
#define COEFF_WORDS 4
#elif __COEFF_WORDS == 5
#define COEFF_WORDS 5
#elif __COEFF_WORDS == 6
#define COEFF_WORDS 6
#elif __COEFF_WORDS == 7
#define COEFF_WORDS 7
#elif __COEFF_WORDS == 8
#define COEFF_WORDS 8
#else
#define COEFF_WORDS __COEFF_WORDS
#endif

#define __COEFF_ID(x) #x
#define _COEFF_ID(x,y) "Z/2^" __COEFF_ID(x) " as mp_limb_t[" __COEFF_ID(y) "]"
#define COEFF_ID _COEFF_ID(MODULUS_EXPONENT,COEFF_WORDS)
#if MODULUS_EXPONENT % GMP_LIMB_BITS == 0
#define COEFF_MASK (~0LL)
#else
#define COEFF_MASK ((1ULL << (MODULUS_EXPONENT % GMP_LIMB_BITS)) - 1)
#endif

struct coeff {
  mp_limb_t data[COEFF_WORDS];
};

/* addition */
inline void coeff_zero(coeff &a) {
  mpn_zero(a.data, COEFF_WORDS);
}

inline bool coeff_z_p(const coeff &a) {
  return mpn_zero_p(a.data, COEFF_WORDS);
}

inline bool coeff_nz_p(const coeff &a) {
  return !coeff_z_p(a);
}

inline void coeff_set(coeff &result, const coeff &a) {
  mpn_copyi(result.data, a.data, COEFF_WORDS);
}

inline void coeff_set_si(coeff &result, const long a) {
  coeff_zero(result);
  if (a >= 0)
    result.data[0] = a;
  else {
    result.data[0] = -a;
    mpn_neg(result.data, result.data, COEFF_WORDS);
    result.data[COEFF_WORDS-1] &= COEFF_MASK;
  }
}

inline long coeff_get_si(const coeff &a) {
  return a.data[0];
}

inline void coeff_init(coeff &a) {
}

inline void coeff_init_set(coeff &result, const coeff &a) {
  coeff_set(result, a);
}

inline void coeff_init_set_si(coeff &result, const long a) {
  coeff_set_si(result, a);
}

inline void coeff_clear(coeff &a) {
}

inline void coeff_add(coeff &result, const coeff &a, const coeff &b) {
  mpn_add_n(result.data, a.data, b.data, COEFF_WORDS);
  result.data[COEFF_WORDS-1] &= COEFF_MASK;
}

inline void coeff_add_si(coeff &result, const coeff &a, long b) {
  if (b >= 0)
    mpn_add_1(result.data, a.data, COEFF_WORDS, b);
  else
    mpn_sub_1(result.data, a.data, COEFF_WORDS, -b);
  result.data[COEFF_WORDS-1] &= COEFF_MASK;
}
inline void coeff_addmul(coeff &result, const coeff &a, const coeff &b) {
  mp_limb_t temp[2*COEFF_WORDS];
  mpn_mul_n(temp, a.data, b.data, COEFF_WORDS);
  mpn_add_n(result.data, result.data, temp, COEFF_WORDS);
  result.data[COEFF_WORDS-1] &= COEFF_MASK;
}

inline int coeff_cmp(const coeff &a, const coeff &b) {
  return mpn_cmp(a.data, b.data, COEFF_WORDS);
}

/* I don't know how to implement a meaningful compare on residue classes. Let's return 0 or 1 */
inline int coeff_cmp_si(const coeff &a, long b) {
  if (b >= 0)
    return a.data[0] != (unsigned long) b || !mpn_zero_p(a.data+1, COEFF_WORDS-1);
  else {
    coeff c;
    mpn_add_1(c.data, a.data, COEFF_WORDS, -b);
    c.data[COEFF_WORDS-1] &= COEFF_MASK;
    return coeff_nz_p(c);
  }
}

inline unsigned __nzlimbs(const mp_limb_t *a, unsigned na) {
  while (na > 0 && a[na-1] == 0) na--;
  return na;
}

inline void __singlebit(coeff &a, unsigned shift) {
  coeff_zero(a);
  a.data[shift / GMP_LIMB_BITS] = 1ULL << (shift % GMP_LIMB_BITS);
}
		     
inline void coeff_fdiv_q(coeff &result, const coeff &a, const coeff &b) {
  unsigned nzlimbs = __nzlimbs(b.data, COEFF_WORDS);
  mp_limb_t q[COEFF_WORDS], r[COEFF_WORDS];
  mpn_tdiv_qr(q, r, 0, a.data, COEFF_WORDS, b.data, nzlimbs);

  mpn_zero(result.data, COEFF_WORDS);
  mpn_copyi(result.data, q, COEFF_WORDS-nzlimbs+1);
}

#ifdef AVOID_MPN_DIVEXACT // internal to gmp >= 6, probably not portable
#define coeff_divexact coeff_fdiv_q
#else
#define mpn_divexact __gmpn_divexact
extern "C" void mpn_divexact (mp_ptr, mp_srcptr, mp_size_t, mp_srcptr, mp_size_t);

inline void coeff_divexact(coeff &result, const coeff &a, const coeff &b) {
  unsigned nzlimbs = __nzlimbs(b.data, COEFF_WORDS);
  coeff_zero(result);
  mpn_divexact(result.data, a.data, COEFF_WORDS, b.data, nzlimbs);
}
#endif

inline void coeff_fdiv_r(coeff &result, const coeff &a, const coeff &b) {
  unsigned nzlimbs = __nzlimbs(b.data, COEFF_WORDS);
  mp_limb_t q[COEFF_WORDS], r[COEFF_WORDS];
  mpn_tdiv_qr(q, r, 0, a.data, COEFF_WORDS, b.data, nzlimbs);

  mpn_zero(result.data, COEFF_WORDS);
  mpn_copyi(result.data, r, nzlimbs);
}

inline void coeff_fdiv_qr(coeff &q, coeff &r, const coeff &a, const coeff &b) {
  unsigned nzlimbs = __nzlimbs(b.data, COEFF_WORDS);
  mp_limb_t mpq[COEFF_WORDS], mpr[COEFF_WORDS];
  mpn_tdiv_qr(mpq, mpr, 0, a.data, COEFF_WORDS, b.data, nzlimbs);

  mpn_zero(q.data, COEFF_WORDS);
  mpn_copyi(q.data, mpq, COEFF_WORDS-nzlimbs+1);
  mpn_zero(r.data, COEFF_WORDS);
  mpn_copyi(r.data, mpr, nzlimbs);
}

inline void coeff_mul(coeff &result, const coeff &a, const coeff &b) {
  mp_limb_t temp[2*COEFF_WORDS];
  mpn_mul_n(temp, a.data, b.data, COEFF_WORDS);
  mpn_copyi(result.data, temp, COEFF_WORDS);
  result.data[COEFF_WORDS-1] &= COEFF_MASK;
}

inline void coeff_mul_si(coeff &result, const coeff &a, long b) {
  mpn_mul_1(result.data, a.data, COEFF_WORDS, b);
  result.data[COEFF_WORDS-1] &= COEFF_MASK;
}

inline void coeff_neg(coeff &result, const coeff &a) {
  mpn_neg(result.data, a.data, COEFF_WORDS);
  result.data[COEFF_WORDS-1] &= COEFF_MASK;
}

/* unused */
inline int coeff_sgn(const coeff &a) {
  return coeff_nz_p(a);
}

inline void coeff_sub(coeff &result, const coeff &a, const coeff &b) {
  mpn_sub_n(result.data, a.data, b.data, COEFF_WORDS);
  result.data[COEFF_WORDS-1] &= COEFF_MASK;
}

inline void coeff_submul(coeff &result, const coeff &a, const coeff &b) {
  mp_limb_t temp[2*COEFF_WORDS];
  mpn_mul_n(temp, a.data, b.data, COEFF_WORDS);
  mpn_sub_n(result.data, result.data, temp, COEFF_WORDS);
  result.data[COEFF_WORDS-1] &= COEFF_MASK;
}

/* addition, unused */
inline void coeff_swap(coeff &a, coeff &b, coeff &tmp) {
  coeff_set(tmp, a);
  coeff_set(a, b);
  coeff_set(b, tmp);
}

inline void inverse_mod_2_k(coeff &result, const coeff &a, unsigned shift) {
  coeff shifteda;

  coeff_zero(shifteda);
  mpn_rshift(shifteda.data, a.data + shift/GMP_LIMB_BITS, COEFF_WORDS - shift/GMP_LIMB_BITS, shift%GMP_LIMB_BITS);

  coeff_set(result, shifteda); // already 3 correct bits
  for (unsigned i = 3; i < MODULUS_EXPONENT; i <<= 1) {
    // result *= 2-shifteda*result
    mp_limb_t temp[2*COEFF_WORDS], temp2[2*COEFF_WORDS];
    mpn_mul_n(temp, shifteda.data, result.data, COEFF_WORDS);
    mpn_sub_1(temp2, temp, COEFF_WORDS, 2);
    mpn_neg(temp, temp2, COEFF_WORDS);
    mpn_mul_n(temp2, result.data, temp, COEFF_WORDS);
    mpn_copyi(result.data, temp2, COEFF_WORDS);
  }
}

inline void coeff_inv(coeff &result, const coeff &a) {
  unsigned aval = coeff_z_p(a) ? -1 : mpn_scan1(a.data, 0);
  if (aval != 0)
    coeff_set_si(result, 0);
  else
    inverse_mod_2_k(result, a, 0);
}

inline void coeff_gcdext(coeff &gcd, coeff &s, coeff &t, const coeff &a, const coeff &b) {
  unsigned aval = coeff_z_p(a) ? -1 : mpn_scan1(a.data, 0),
    bval = mpn_scan1(b.data, 0);

  if (aval >= bval) {
    __singlebit(gcd, bval);
    mpn_zero(s.data, COEFF_WORDS);
    inverse_mod_2_k(t, b, bval);
  } else {
    __singlebit(gcd, aval);
    inverse_mod_2_k(s, a, aval);
    mpn_zero(t.data, COEFF_WORDS);
  }
}

/* addition, returns true if a in [0,b) or b=0 */
inline bool coeff_reduced_p(const coeff &a, const coeff &b) {
  return coeff_z_p(b) || coeff_cmp(a, b) < 0;
}

/* addition, returns unit and generator of annihilator ideal:
   a*unit is canonical (2^n) and a*annihilator=0 */
inline void coeff_unit_annihilator(coeff &unit, coeff &annihilator, const coeff &a) {
  if (coeff_z_p(a)) {
    coeff_set_si(unit, 0);
    coeff_set_si(annihilator, 1);
    return;
  }
  unsigned shift = mpn_scan1(a.data, 0);
  inverse_mod_2_k(unit, a, shift);
  if (shift > 0)
    __singlebit(annihilator, MODULUS_EXPONENT - shift);
  else
    mpn_zero(annihilator.data, COEFF_WORDS);
}

inline int coeff_out_str(FILE *f, const coeff &a)
{
  mp_limb_t temp[COEFF_WORDS];
  mpn_copyi(temp, a.data, COEFF_WORDS);
  unsigned nzlimbs = __nzlimbs(temp, COEFF_WORDS);
  size_t digits = mpn_sizeinbase(temp, nzlimbs, 10);
  unsigned char str[digits+1];
  digits = mpn_get_str(str, 10, temp, nzlimbs);
  for (unsigned i = 0; i < digits; i++)
    str[i] += '0';
  str[digits] = 0;
  fprintf(f, "%s", str); /* maybe we should print in binary or hex? */
  return digits;
}

#define coeff_base 2

inline void coeff_set_str(coeff &a, const char *s, int base)
{
  coeff_set_si(a, 0);

  if (*s == '0') base = coeff_base;
  
  while (isalnum(*s)) {
    coeff_mul_si(a, a, base);
    coeff_add_si(a, a, isdigit(*s) ? *s - '0' : *s + 10 - (isupper(*s) ? 'A' : 'a'));
    s++;
  }
}
