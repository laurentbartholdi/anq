/******************************************************************************
**
**               Nilpotent Quotient for Lie Algebras
** coeff_p_k.h
** defines coefficients as residues modulo p^k
*/

#include <inttypes.h>

#if !defined(MODULUS_PRIME) || !defined(MODULUS_EXPONENT)
#error You must specify MODULUS_PRIME AND MODULUS_EXPONENT
#include </> // abort
#endif

#define __COEFF_ID(x) #x
#define _COEFF_ID(x,y) "Z/" __COEFF_ID(x) "^" __COEFF_ID(y) " as uint64_t"
#define COEFF_ID _COEFF_ID(MODULUS_PRIME,MODULUS_EXPONENT)

#if 0 // nice exercise in template programming
const uint64_t PRIME = MODULUS_PRIME;
const uint64_t EXPONENT = MODULUS_EXPONENT;
template<int X, int P> struct intpow { enum { result = X*intpow<X,P-1>::result }; };
template<int X> struct intpow<X,0> { enum { result = 1 }; };
const uint64_t MODULUS = intpow<PRIME,EXPONENT>::result;
#endif

struct coeff {
  uint64_t data;
};
typedef unsigned __int128 uint128_t; // for intermediate results
typedef signed __int128 int128_t; // for intermediate results

/*      UINT64_MAX 18446744073709551615ULL */
#define P10_UINT64 10000000000000000000ULL   /* 19 zeroes */
#define E10_UINT64 19

#define STRINGIZER(x)   # x
#define TO_STRING(x)    STRINGIZER(x)

/* unused, for debugging purposes */
static int print_u128_t(uint128_t u128)
{
    int rc;
    if (u128 > UINT64_MAX)
    {
        uint128_t leading  = u128 / P10_UINT64;
        uint64_t  trailing = u128 % P10_UINT64;
        rc = print_u128_t(leading);
        rc += printf("%." TO_STRING(E10_UINT64) PRIu64, trailing);
    }
    else
    {
        uint64_t u64 = u128;
        rc = printf("%" PRIu64, u64);
    }
    return rc;
}

constexpr inline uint64_t powint(uint64_t x, uint64_t p) {
  return p ? (p & 1 ? x : 1)*powint(x*x, p>>1) : 1;
}

constexpr inline uint64_t montgomery_gcd(uint64_t a, uint64_t b) {
  return a ? montgomery_gcd(b%a, a) : b;
}

/* returns the s such that s*a + t*b = (a,b).
   invoke with montgomery_gcdext(a, b, 1, 0, 0, 1).
   recursion invariant is s*a0 + t*b0 = a, u*a0 + v*b0 = b.
*/
constexpr inline int128_t montgomery_gcdext(uint128_t a, uint128_t b, int128_t s, int128_t t, int128_t u, int128_t v) {
  return a ? montgomery_gcdext(b%a, a, u-(b/a)*s, v-(b/a)*t, s, t) : u;
}

const uint64_t MONTGOMERY_N = powint(MODULUS_PRIME, MODULUS_EXPONENT);
const uint128_t MONTGOMERY_R = ((uint128_t) 1) << 64;
const uint64_t MONTGOMERY_RR = ((MONTGOMERY_R % MONTGOMERY_N) * (MONTGOMERY_R % MONTGOMERY_N)) % MONTGOMERY_N;
const uint64_t MONTGOMERY_RINV = (montgomery_gcdext(MONTGOMERY_R, MONTGOMERY_N, 1, 0, 0, 1) + MONTGOMERY_N) % MONTGOMERY_N;
const uint64_t MONTGOMERY_NPRIME = -montgomery_gcdext(MONTGOMERY_N, MONTGOMERY_R, 1, 0, 0, 1);

const inline uint64_t montgomery_redc(uint128_t T) {
  uint64_t m = ((uint64_t) T)*MONTGOMERY_NPRIME;
  uint64_t t = (T + (uint128_t) m*MONTGOMERY_N) >> 64;
  //  printf("m=%llu, t=%llu: ",m,t);
  //  print_u128_u(T + (uint128_t) m*(uint128_t) MONTGOMERY_N); printf("\n");
  return (t >= MONTGOMERY_N) ? t - MONTGOMERY_N : t;
}

const inline coeff long2coeff(long l) {
  return { .data = montgomery_redc((uint128_t) MONTGOMERY_RR * (uint128_t) l) };
}

const inline long coeff2long2(coeff c) {
  return montgomery_redc(c.data);
}

const inline coeff uint64_t2coeff(uint64_t l) {
  return { .data = montgomery_redc((uint128_t) MONTGOMERY_RR * (uint128_t) l) };
}

const inline uint64_t coeff2uint64_t(coeff c) {
  return montgomery_redc(c.data);
}

/****************************************************************/
inline void coeff_set_si(coeff &, const long);
inline void coeff_mul(coeff &, const coeff &, const coeff &);

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
  coeff_set_si(result, a);
}

inline void coeff_set(coeff &result, const coeff &a) {
  result.data = a.data;
}

inline void coeff_set_si(coeff &result, const long a) {
  result = long2coeff(a);
}

inline long coeff_get_si(const coeff &a) {
  return montgomery_redc(a.data);
}

inline void coeff_clear(coeff &a) {
}

inline void coeff_add(coeff &result, const coeff &a, const coeff &b) {
  uint128_t sum = (uint128_t) a.data + b.data;
  if (sum >= MONTGOMERY_N)
    result.data = sum - MONTGOMERY_N;
  else
    result.data = sum;
}

inline void coeff_add_si(coeff &result, const coeff &a, long b) {
  coeff_add(result, a, long2coeff(b));
}

inline void coeff_addmul(coeff &result, const coeff &a, const coeff &b) {
  coeff c;
  coeff_mul(c, a, b);
  coeff_add(result, result, c);
}

inline int coeff_cmp(const coeff &a, const coeff &b) {
  return (a.data > b.data) - (a.data < b.data);
}

inline int coeff_cmp_si(const coeff &a, long b) {
  return coeff_cmp(a, long2coeff(b));
}

inline void coeff_divexact(coeff &result, const coeff &a, const coeff &b) {
  result.data = a.data / coeff2uint64_t(b);
}

inline void coeff_fdiv_q(coeff &result, const coeff &a, const coeff &b) {
  result = uint64_t2coeff(coeff2uint64_t(a) / coeff2uint64_t(b));
}

inline void coeff_fdiv_r(coeff &result, const coeff &a, const coeff &b) {
  result = uint64_t2coeff(coeff2uint64_t(a) % coeff2uint64_t(b));
}

inline void coeff_mul(coeff &result, const coeff &a, const coeff &b) {
  result.data = montgomery_redc((uint128_t) a.data * b.data);
}

inline void coeff_mul_si(coeff &result, const coeff &a, long b) {
  coeff_mul(result, a, long2coeff(b));
}

inline void coeff_neg(coeff &result, const coeff &a) {
  if (a.data == 0)
    result.data = 0;
  else
    result.data = MONTGOMERY_N - a.data;
}

/* unused */
inline int coeff_sgn(const coeff &a) {
  return a.data != 0;
}

inline void coeff_sub(coeff &result, const coeff &a, const coeff &b) {
  coeff_add(result, a, { .data = MONTGOMERY_N - b.data });
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

/* don't worry about (tail) recursion, gcc changes it to iteration */
const inline int64_t inverse_mod_p_rec(uint64_t a, uint64_t b, int64_t s, int64_t u) {
  return a ? inverse_mod_p_rec(b%a, a, u-(b/a)*s, s) : u;
}
const inline uint64_t inverse_mod_p(uint64_t a) {
  int64_t i = inverse_mod_p_rec(a, MODULUS_PRIME, 1, 0);
  if (i < 0) return i + MODULUS_PRIME; else return i;
}
				   
const inline coeff coeff_inverse_mod_si(uint64_t va) {
  coeff a = uint64_t2coeff(va);
  coeff inverse =
#if MODULUS_PRIME == 2
#error Use COEFF_IS_MOD2_64 for MODULUS_PRIME=2
#elif MODULUS_PRIME > 7
  uint64_t2coeff(inverse_mod_p(va));
#else
    a;
#if MODULUS_PRIME == 3 // a == a^-1 mod 3
#elif MODULUS_PRIME == 5 // a^3 == a^-1 mod 5
  coeff_mul(inverse, inverse, a);
  coeff_mul(inverse, inverse, a);
#elif MODULUS_PRIME == 7 // a^5 == a^-1 mod 7
  {
    coeff aa = a;
    coeff_mul(aa, a, a);
    coeff_mul(inverse, inverse, aa);
    coeff_mul(inverse, inverse, aa);
  }
#endif
#endif
  for (unsigned i = 1; i < MODULUS_EXPONENT; i <<= 1) {
    coeff temp = long2coeff(2);
    coeff_submul(temp, a, inverse);
    coeff_mul(inverse, inverse, temp);
  }
  return inverse;
}

const inline void coeff_gcdext(coeff &gcd, coeff &s, coeff &t, const coeff &a, const coeff &b) {
  uint64_t va = coeff2uint64_t(a), vb = coeff2uint64_t(b), vgcd = 1;

  /* this could be written in log(MODULUS_EXPONENT) steps rather than MODULUS_EXPONENT */
  while (va % MODULUS_PRIME == 0 && vb % MODULUS_PRIME == 0) {
    va /= MODULUS_PRIME;
    vb /= MODULUS_PRIME;
    vgcd *= MODULUS_PRIME;
  }

  gcd = uint64_t2coeff(vgcd);

  if (va % MODULUS_PRIME == 0) {
    s.data = 0;
    t = coeff_inverse_mod_si(vb);
  } else {
    s = coeff_inverse_mod_si(va);
    t.data = 0;
  }
}   

/* addition, returns true if a in [0,b) or b=0 */
const inline bool coeff_reduced_p(const coeff &a, const coeff &b) {
  if (b.data == 0)
    return true;
  return coeff2uint64_t(a) < coeff2uint64_t(b);
}

/* addition, returns unit and generator of annihilator ideal:
   a*unit is canonical (2^n) and a*annihilator=0 */
const inline void coeff_unit_annihilator(coeff &unit, coeff &annihilator, const coeff &a) {
  uint64_t va = coeff2uint64_t(a), vgcd = 1;

  if (va == 0) {
    unit = uint64_t2coeff(0);
    annihilator = uint64_t2coeff(1);
    return;
  }

  /* this could be written in log(MODULUS_EXPONENT) steps rather than MODULUS_EXPONENT */
  while (va % MODULUS_PRIME == 0) {
    va /= MODULUS_PRIME;
    vgcd *= MODULUS_PRIME;
  }

  unit = coeff_inverse_mod_si(va);
  annihilator = uint64_t2coeff(MONTGOMERY_N / vgcd);
}

inline int coeff_out_str(FILE *f, const coeff &a)
{
  return fprintf(f, "%ld", coeff_get_si(a)); /* maybe we should print in base MODULUS_PRIME? */
}

#define coeff_base MODULUS_PRIME
