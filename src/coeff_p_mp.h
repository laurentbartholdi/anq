/******************************************************************************
**
**               Nilpotent Quotient for Lie Algebras
** coeff_p_mp.h
** defines coefficients as residues modulo p^k
*/

#include <gmp.h>

#if !defined(MODULUS_PRIME) || !defined(MODULUS_EXPONENT)
#error You must specify MODULUS_PRIME AND MODULUS_EXPONENT
#include </> // abort
#endif

#ifndef COEFF_WORDS
#define __COEFF_WORDS (MODULUS_EXPONENT + MODULUS_MAXEXPONENT - 1)/MODULUS_MAXEXPONENT
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
#endif

#define __COEFF_ID(x) #x
#define _COEFF_ID(x,y,z) "Z/" __COEFF_ID(x) "^" __COEFF_ID(y) " as mp_limb_t[" __COEFF_ID(z) "]"
#define COEFF_ID _COEFF_ID(MODULUS_PRIME,MODULUS_EXPONENT,COEFF_WORDS)

struct coeff {
  mp_limb_t data[COEFF_WORDS];
};

struct doublecoeff {
  mp_limb_t data[2*COEFF_WORDS];
};

inline coeff __mpn_ui(unsigned i) {
  coeff c;
  mpn_zero(c.data, COEFF_WORDS);
  c.data[0] = i;
  return c;
}

inline coeff __mpn_pow_ui(coeff x, unsigned p) {
  if (p) {
    doublecoeff sqr;
    mpn_sqr(sqr.data, x.data, COEFF_WORDS);
    coeff c;
    mpn_copyi(c.data, sqr.data, COEFF_WORDS);
    if (p & 1) {
      mpn_mul_n(sqr.data, c.data, x.data, COEFF_WORDS);
      mpn_copyi(c.data, sqr.data, COEFF_WORDS);
    }
    return c;
  } else
    return __mpn_ui(1);
}

const coeff MONTGOMERY_N = __mpn_pow_ui(__mpn_ui(MODULUS_PRIME), MODULUS_EXPONENT);

#if 0 // Montgomery arithmetic -- doesn't seem worth it
inline doublecoeff __montgomery_r(void) {
  doublecoeff c;
  mpn_zero(c.data, 2*COEFF_WORDS);
  c.data[COEFF_WORDS] = 1;
  return c;
}
const doublecoeff MONTGOMERY_R = __montgomery_r();

inline doublecoeff __montgomery_rr(void) {
  doublecoeff q, r, rr;

  // sanity check, do it once
  if (MONTGOMERY_N.data[COEFF_WORDS-1] == 0) {
    fprintf(stderr, "COEFF_WORDS is too large; decrease and recompile");
    volatile int zero = 0;
    fprintf(stderr, "%d", zero / zero); // BOOM!
  }

  mpn_tdiv_qr(q.data, r.data, 0, MONTGOMERY_R.data, 2*COEFF_WORDS, MONTGOMERY_N.data, COEFF_WORDS);
  mpn_sqr(rr.data, r.data, COEFF_WORDS);
  mpn_tdiv_qr(q.data, r.data, 0, rr.data, 2*COEFF_WORDS, MONTGOMERY_N.data, COEFF_WORDS);
  mpn_zero(r.data+COEFF_WORDS, COEFF_WORDS);
  return r;
}
const doublecoeff MONGOMERY_RR = __montgomery_rr();

coeff __montgomery_rinv(void) {
  doublecoeff g, s, t;
  mpn_zero(g.data, 2*COEFF_WORDS);
  mpn_zero(s.data, 2*COEFF_WORDS);
   
  mp_size_t slen;
  mpn_gcdext(g.data, s.data, &slen, MONTGOMERY_R.data, COEFF_WORDS+1, MONTGOMERY_N.data, COEFF_WORDS);
}
const coeff MONTGOMERY_RINV = __montgomery_rinv();

coeff __montgomery_nprime(void) {
  return __mpn_ui(0);
}
const coeff MONTGOMERY_NPRIME = __montgomery_nprime();
#endif

inline void __reduce(coeff &result, doublecoeff a, unsigned len)
{
  coeff q;
  mpn_tdiv_qr(q.data, result.data, 0, a.data, len, MONTGOMERY_N.data, COEFF_WORDS);
}

/****************************************************************/
inline void coeff_set_si(coeff &, const long);
inline void coeff_mul(coeff &, const coeff &, const coeff &);

/* addition */
inline void coeff_zero(coeff &a) {
  coeff_zero(a);
}

inline bool coeff_nz_p(const coeff &a) {
  return !mpn_zero_p(a.data, COEFF_WORDS);
}

inline bool coeff_z_p(const coeff &a) {
  return !coeff_nz_p(a);
}

inline void coeff_set(coeff &result, const coeff &a) {
  mpn_copyi(result.data, a.data, COEFF_WORDS);
}

inline void coeff_set_si(coeff &result, const long a) {
  coeff_zero(result);
  result.data[0] = a;
  if (a < 0)
    mpn_add_n(result.data, result.data, MONTGOMERY_N.data, COEFF_WORDS);
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
  mp_limb_t carry = mpn_add_n(result.data, a.data, b.data, COEFF_WORDS);

  if (carry || mpn_cmp(MONTGOMERY_N.data, result.data, COEFF_WORDS) >= 0)
    mpn_sub_n(result.data, result.data, MONTGOMERY_N.data, COEFF_WORDS);
}

inline void coeff_add_si(coeff &result, const coeff &a, long b) {
  if (b >= 0) {
    mp_limb_t carry = mpn_add_1(result.data, a.data, COEFF_WORDS, b);
    if (carry || mpn_cmp(MONTGOMERY_N.data, result.data, COEFF_WORDS) >= 0)
      mpn_sub_n(result.data, result.data, MONTGOMERY_N.data, COEFF_WORDS);
  } else {
    mp_limb_t carry = mpn_sub_1(result.data, a.data, COEFF_WORDS, -b);
    if (carry)
      mpn_add_n(result.data, result.data, MONTGOMERY_N.data, COEFF_WORDS);
  }
}

inline void coeff_addmul(coeff &result, const coeff &a, const coeff &b) {
  coeff c;
  coeff_mul(c, a, b);
  coeff_add(result, result, c);
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
    return mpn_cmp(c.data, MONTGOMERY_N.data, COEFF_WORDS);
  }
}

inline unsigned __nzlimbs(const mp_limb_t *a, unsigned na) {
  while (na > 0 && a[na-1] == 0) na--;
  return na;
}

inline void coeff_fdiv_q(coeff &result, const coeff &a, const coeff &b) {
  unsigned nzlimbs = __nzlimbs(b.data, COEFF_WORDS);
  mp_limb_t q[COEFF_WORDS], r[COEFF_WORDS];
  mpn_tdiv_qr(q, r, 0, a.data, COEFF_WORDS, b.data, nzlimbs);

  coeff_zero(result);
  mpn_copyi(result.data, q, COEFF_WORDS-nzlimbs+1);
}

inline void coeff_divexact(coeff &result, const coeff &a, const coeff &b) {
  return coeff_fdiv_q(result, a, b);
  // we should be able to call mpn_divexact !!!
}

inline void coeff_fdiv_r(coeff &result, const coeff &a, const coeff &b) {
  unsigned nzlimbs = __nzlimbs(b.data, COEFF_WORDS);
  mp_limb_t q[COEFF_WORDS], r[COEFF_WORDS];
  mpn_tdiv_qr(q, r, 0, a.data, COEFF_WORDS, b.data, nzlimbs);

  coeff_zero(result);
  mpn_copyi(result.data, r, nzlimbs);
}

inline void coeff_mul(coeff &result, const coeff &a, const coeff &b) {
  doublecoeff temp;
  mpn_mul_n(temp.data, a.data, b.data, COEFF_WORDS);
  __reduce(result, temp, 2*COEFF_WORDS);
}

inline void coeff_mul_si(coeff &result, const coeff &a, long b) {
  doublecoeff temp;
  temp.data[COEFF_WORDS] = mpn_mul_1(temp.data, a.data, COEFF_WORDS, b);
  __reduce(result, temp, COEFF_WORDS+1);
}

inline void coeff_neg(coeff &result, const coeff &a) {
  if (coeff_z_p(a))
    coeff_zero(result);
  else
    mpn_sub_n(result.data, MONTGOMERY_N.data, a.data, COEFF_WORDS);
}

/* unused */
inline int coeff_sgn(const coeff &a) {
  return coeff_nz_p(a);
}

inline void coeff_sub(coeff &result, const coeff &a, const coeff &b) {
  mp_limb_t carry = mpn_sub_n(result.data, a.data, b.data, COEFF_WORDS);
  if (carry)
    mpn_add_n(result.data, result.data, MONTGOMERY_N.data, COEFF_WORDS);
}

inline void coeff_submul(coeff &result, const coeff &a, const coeff &b) {
  coeff c;
  coeff_mul(c, a, b);
  coeff_sub(result, result, c);
}

/* addition, unused */
inline void coeff_swap(coeff &a, coeff &b, coeff &tmp) {
  coeff_set(tmp, a);
  coeff_set(a, b);
  coeff_set(b, tmp);
}

/* addition, modular inverse. result*a == 1 mod MONTGOMERY_N */
inline void coeff_inverse(coeff &result, const coeff &a) {
  coeff g;
  doublecoeff s;
  mp_size_t slen;
  {
    coeff a0 = a, m0 = MONTGOMERY_N;
    mpn_gcdext(g.data, s.data, &slen, a0.data, COEFF_WORDS, m0.data, COEFF_WORDS);
  }
  coeff_zero(result);
  if (slen < 0)
    mpn_add(result.data, MONTGOMERY_N.data, COEFF_WORDS, s.data, slen);
  else
    mpn_copyi(result.data, s.data, slen);
}

inline unsigned coeff_pval(const coeff &a) {
  coeff c = a;
  unsigned val = 0;

  /* optimize: at minimum, divide by chunks of MODULUS_MAXEXPONENT first */
  while (mpn_divrem_1(c.data, 0, c.data, COEFF_WORDS, MODULUS_PRIME) == 0)
    val++;

  return val;
}
  
/* gcd = s*a + t*b */
const inline void coeff_gcdext(coeff &gcd, coeff &s, coeff &t, const coeff &a, const coeff &b) {
  coeff_set_si(gcd, 1);

  coeff c[2], d[2];
  bool parity = false;
  c[parity] = a;
  d[parity] = b;

  for (;;) {
    mp_limb_t ra = mpn_divrem_1(c[!parity].data, 0, c[parity].data, COEFF_WORDS, MODULUS_PRIME);
    mp_limb_t rb = mpn_divrem_1(d[!parity].data, 0, d[parity].data, COEFF_WORDS, MODULUS_PRIME);
    if (rb != 0) {
      coeff_zero(s);
      coeff_inverse(t, d[parity]);
      break;
    } else if (ra != 0) {
      coeff_inverse(s, c[parity]);
      coeff_zero(t);
      break;
    }
    mpn_mul_1(gcd.data, gcd.data, COEFF_WORDS, MODULUS_PRIME);
    parity = !parity;
  }
}

/* addition, returns true if a in [0,b) or b=0 */
const inline bool coeff_reduced_p(const coeff &a, const coeff &b) {
  return coeff_z_p(b) || coeff_cmp(a, b) < 0;
}

/* addition, returns unit and generator of annihilator ideal:
   a*unit is canonical (MODULUS_PRIME^n) and a*annihilator=0 */
const inline void coeff_unit_annihilator(coeff &unit, coeff &annihilator, const coeff &a) {
  if (coeff_z_p(a)) {
    coeff_zero(unit);
    coeff_set_si(annihilator, 1);
    return;
  }
  
  coeff c[2];
  bool parity = false, first = true;
  coeff_set(annihilator, MONTGOMERY_N);  
  c[parity] = a;

  for (;;) {
    mp_limb_t ra = mpn_divrem_1(c[!parity].data, 0, c[parity].data, COEFF_WORDS, MODULUS_PRIME);
    if (ra != 0) {
      coeff_inverse(unit, c[parity]);
      if (first)
	coeff_zero(annihilator);
      break;
    }
    mpn_divexact_1(annihilator.data, annihilator.data, COEFF_WORDS, MODULUS_PRIME);
    parity = !parity;
    first = false;
  }
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
  fprintf(f, "%s", str); /* maybe we should print in base MODULUS_PRIME? */
  return digits;
}

#define coeff_base MODULUS_PRIME
