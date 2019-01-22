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
  coeff c = __mpn_ui(1);
  while (p) {
    doublecoeff temp;
    if (p & 1) {
      mpn_mul_n(temp.data, c.data, x.data, COEFF_WORDS);
      mpn_copyi(c.data, temp.data, COEFF_WORDS);
    }
    mpn_sqr(temp.data, x.data, COEFF_WORDS);
    mpn_copyi(x.data, temp.data, COEFF_WORDS);
    p >>= 1;
  }
  return c;
}

const coeff COEFF_N = __mpn_pow_ui(__mpn_ui(MODULUS_PRIME), MODULUS_EXPONENT);

#if 0 // Montgomery arithmetic -- doesn't seem worth it
const coeff MONTGOMERY_N = COEFF_N;

const doublecoeff MONTGOMERY_R = []{
  doublecoeff c;
  mpn_zero(c.data, 2*COEFF_WORDS);
  c.data[COEFF_WORDS] = 1;
  return c;
}();

const doublecoeff MONGOMERY_RR = []{
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
}();

const coeff MONTGOMERY_RINV = []{
}();

const coeff MONTGOMERY_NPRIME = []{
}();
#endif

inline void __reduce(coeff &result, doublecoeff a, unsigned len)
{
  doublecoeff q;
  mpn_tdiv_qr(q.data, result.data, 0, a.data, len, COEFF_N.data, COEFF_WORDS);
}

inline unsigned __nzlimbs(const mp_limb_t *a, unsigned na) {
  while (na > 0 && a[na-1] == 0) na--;
  return na;
}

/****************************************************************/
inline void coeff_set_si(coeff &, const long);
inline void coeff_mul(coeff &, const coeff &, const coeff &);

/* addition */
inline void coeff_zero(coeff &a) {
  mpn_zero(a.data, COEFF_WORDS);
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
  if (a >= 0) {
    coeff_zero(result);
    result.data[0] = a;
  } else
    mpn_sub_1(result.data, COEFF_N.data, COEFF_WORDS, -a);
}

inline long coeff_get_si(const coeff &a) {
#if COEFF_WORDS > 1
  if (a.data[COEFF_WORDS-1] == COEFF_N.data[COEFF_WORDS-1])
#else
  if (a.data[0] > COEFF_N.data[0] / 2)
#endif
    return a.data[0] - (long) COEFF_N.data[0];
  else
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

  if (carry || mpn_cmp(result.data, COEFF_N.data, COEFF_WORDS) >= 0)
    mpn_sub_n(result.data, result.data, COEFF_N.data, COEFF_WORDS);
}

inline void coeff_add_si(coeff &result, const coeff &a, long b) {
  if (b >= 0) {
    mp_limb_t carry = mpn_add_1(result.data, a.data, COEFF_WORDS, b);
    if (carry || mpn_cmp(result.data, COEFF_N.data, COEFF_WORDS) >= 0)
      mpn_sub_n(result.data, result.data, COEFF_N.data, COEFF_WORDS);
  } else {
    mp_limb_t carry = mpn_sub_1(result.data, a.data, COEFF_WORDS, -b);
    if (carry)
      mpn_add_n(result.data, result.data, COEFF_N.data, COEFF_WORDS);
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
    return coeff_cmp(c, COEFF_N);
  }
}

inline void coeff_fdiv_q(coeff &result, const coeff &a, const coeff &b) {
  unsigned nzlimbs = __nzlimbs(b.data, COEFF_WORDS);
  coeff r;
  coeff_zero(result);
  mpn_tdiv_qr(result.data, r.data, 0, a.data, COEFF_WORDS, b.data, nzlimbs);
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
  coeff q;
  coeff_zero(result);
  mpn_tdiv_qr(q.data, result.data, 0, a.data, COEFF_WORDS, b.data, nzlimbs);
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
    mpn_sub_n(result.data, COEFF_N.data, a.data, COEFF_WORDS);
}

/* unused */
inline int coeff_sgn(const coeff &a) {
  return coeff_nz_p(a);
}

inline void coeff_sub(coeff &result, const coeff &a, const coeff &b) {
  mp_limb_t carry = mpn_sub_n(result.data, a.data, b.data, COEFF_WORDS);
  if (carry)
    mpn_add_n(result.data, result.data, COEFF_N.data, COEFF_WORDS);
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

/* addition, modular inverse. result*a == 1 mod COEFF_N */
inline void coeff_inv(coeff &result, const coeff &a) {
  coeff g;
  doublecoeff s;
  mp_size_t slen;
  {
    coeff a0 = a, m0 = COEFF_N;
    mpn_gcdext(g.data, s.data, &slen, a0.data, COEFF_WORDS, m0.data, COEFF_WORDS);
  }
  coeff_zero(result);
  if (slen < 0)
    mpn_sub(result.data, COEFF_N.data, COEFF_WORDS, s.data, -slen);
  else
    mpn_copyi(result.data, s.data, slen);
}

constexpr inline mp_limb_t powint(mp_limb_t x, mp_limb_t p) {
  return p ? (p & 1 ? x : 1)*powint(x*x, p>>1) : 1;
}

const mp_limb_t MODULUS_POWERS2[] = { MODULUS_PRIME,
				  powint(MODULUS_PRIME,2),
				  powint(MODULUS_PRIME,4),
				  powint(MODULUS_PRIME,8),
				  powint(MODULUS_PRIME,16),
				  powint(MODULUS_PRIME,32) };
constexpr inline unsigned lgint(mp_limb_t n) {
  return n ? 1+lgint(n/2) : -1;
}
const mp_limb_t MODULUS_POWMAX = powint(MODULUS_PRIME,MODULUS_MAXEXPONENT);
const unsigned logMODULUS_MAXEXPONENT = lgint(MODULUS_MAXEXPONENT);

/* addition, MODULUS_PRIME-valuation of a.
   Set result to a / largest power of MODULUS_PRIME dividing it */
const inline unsigned coeff_val(coeff &result, const coeff &a) {
  if (coeff_z_p(a))
    return MODULUS_EXPONENT; // or infinity
  
  coeff c[2];
  c[0] = a;
  bool parity = false;
    unsigned val = 0;

  while (mpn_divrem_1(c[!parity].data, 0, c[parity].data, COEFF_WORDS, MODULUS_POWMAX) == 0) {
    val += MODULUS_MAXEXPONENT;
    parity = !parity;
  }

  for (int i = logMODULUS_MAXEXPONENT; i >= 0; i--)
    if (mpn_divrem_1(c[!parity].data, 0, c[parity].data, COEFF_WORDS, MODULUS_POWERS2[i]) == 0) {
      val += 1 << i;
      parity = !parity;
    }

  result = c[parity];
  return val;
}
  
/* gcd = s*a + t*b */
const inline void coeff_gcdext(coeff &gcd, coeff &s, coeff &t, const coeff &a, const coeff &b) {
#if 0 // 0 has valuation MODULUS_EXPONENT, everything fine
  if (coeff_z_p(a)) {
    coeff_set(gcd, b);
    coeff_set_si(s, 0);
    coeff_set_si(t, 1);
    return;
  }
  if (coeff_z_p(b)) {
    coeff_set(gcd, a);
    coeff_set_si(s, 1);
    coeff_set_si(t, 0);
    return;
  }
#endif

  coeff va, vb;
  unsigned vala = coeff_val(va, a), valb = coeff_val(vb, b);

  if (vala > valb) {
    gcd = __mpn_pow_ui(__mpn_ui(MODULUS_PRIME), valb);
    coeff_zero(s);
    coeff_inv(t, vb);
  } else {
    gcd = __mpn_pow_ui(__mpn_ui(MODULUS_PRIME), vala);
    coeff_inv(s, va);
    coeff_zero(t);
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

  coeff va;
  unsigned vala = coeff_val(va, a);
  coeff_inv(unit, va);
  annihilator = __mpn_pow_ui(__mpn_ui(MODULUS_PRIME), MODULUS_EXPONENT-vala);
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
