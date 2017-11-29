/******************************************************************************
**
**               Nilpotent Quotient for Lie Algebras
** coeff_2_64.h
** defines coefficients as signed 64-bit integers
*/

struct coeff {
  uint64_t data;
};

/* addition */
inline bool coeff_nz(const coeff &a) {
  return a.data != 0;
}

inline void coeff_init(coeff &a) {
}

inline void coeff_init_set(coeff &result, const coeff &a) {
  result.data = a.data;
}

inline void coeff_init_set_si(coeff &result, const long a) {
  result.data = a;
}

inline void coeff_set(coeff &result, const coeff &a) {
  result.data = a.data;
}

inline void coeff_set_si(coeff &result, const long a) {
  result.data = a;
}

inline long coeff_get_si(coeff &a) {
  return a.data;
}

inline void coeff_clear(coeff &a) {
}

inline void coeff_add(coeff &result, const coeff &a, const coeff &b) {
  result.data = a.data + b.data;
}

inline void coeff_add_si(coeff &result, const coeff &a, long b) {
  result.data = a.data + b;
}
inline void coeff_addmul(coeff &result, const coeff &a, const coeff &b) {
  result.data += a.data * b.data;
}

inline int coeff_cmp(const coeff &a, const coeff &b) {
  return (a.data > b.data) - (a.data < b.data);
}

/* I don't know how to implement a meaningful compare on residue classes. Let's return 0 or 1 */
inline int coeff_cmp_si(const coeff &a, long b) {
  return a.data != (unsigned long) b; 
}

inline void coeff_divexact(coeff &result, const coeff &a, const coeff &b) {
  result.data = a.data / b.data;
}

inline void coeff_fdiv_q(coeff &result, const coeff &a, const coeff &b) {
  result.data = a.data / b.data;
}

inline void coeff_mul(coeff &result, const coeff &a, const coeff &b) {
  result.data = a.data * b.data;
}

inline void coeff_mul_si(coeff &result, const coeff &a, long b) {
  result.data = a.data * b;
}

inline void coeff_neg(coeff &result, const coeff &a) {
  result.data = -a.data;
}

/* unused */
inline int coeff_sgn(const coeff &a) {
  return a.data > 0;
}

inline void coeff_sub(coeff &result, const coeff &a, const coeff &b) {
  result.data = a.data - b.data;
}

inline void coeff_submul(coeff &result, const coeff &a, const coeff &b) {
  result.data -= a.data * b.data;
}

/* addition, unused */
inline void coeff_swap(coeff &a, coeff &b, coeff &tmp) {
  coeff_set(tmp, a);
  coeff_set(a, b);
  coeff_set(b, tmp);
}

inline unsigned long inverse_mod_2(unsigned long a) {
  unsigned long inverse = a; // already 3 correct bits
  for (unsigned i = 0; i < 5; i++)
    inverse *= 2 - a*inverse;
  return inverse;
}

inline void coeff_gcdext(coeff &gcd, coeff &s, coeff &t, const coeff &a, const coeff &b) {
  unsigned long aval = a.data & -a.data, bval = b.data & -b.data;
  if (a.data == 0 || aval >= bval) {
    gcd.data = bval;
    s.data = 0;
    t.data = inverse_mod_2(b.data >> __builtin_ctzl(bval)); // b.data / bval
  } else {
    gcd.data = aval;
    s.data = inverse_mod_2(a.data >> __builtin_ctzl(aval));
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
  int shift = __builtin_ctzl(a.data);
  unit.data = inverse_mod_2(a.data >> shift);
  int shift0 = shift >> 1; /* beware, shifting by 64 is a no-op */
  annihilator.data = (1ULL << (32-shift0)) << (32+shift0-shift);
}
