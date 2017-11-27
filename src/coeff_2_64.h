/******************************************************************************
**
**               Nilpotent Quotient for Lie Algebras
** coeff_long.h
** defines coefficients as signed 64-bit integers
*/

struct coeff {
#ifdef MOD2
  unsigned
#endif
  long data;
  coeff() = default;
  coeff(long d) { data = d; }
  bool notone(void) const { return this->data != 1; }
  bool notzero(void) const { return this->data != 0; }
};
typedef coeff *coeffvec;

inline void coeff_neg(coeff &result, const coeff &a) {
  result.data = -a.data;
}

inline void coeff_add(coeff &result, const coeff &a, const coeff &b) {
  result.data = a.data + b.data;
}

inline void coeff_sub(coeff &result, const coeff &a, const coeff &b) {
  result.data = a.data - b.data;
}

inline void coeff_mul(coeff &result, const coeff &a, const coeff &b) {
  result.data = a.data * b.data;
}

inline void coeff_addmul(coeff &result, const coeff &a, const coeff &b, const coeff &c) {
  result.data = a.data + b.data * c.data;
}

inline void coeff_submul(coeff &result, const coeff &a, const coeff &b, const coeff &c) {
  result.data = a.data - b.data * c.data;
}

inline void coeff_clear(coeff &c) {
}

inline void coeff_init(coeff &c) {
}

  coeff reduce(coeff c) { /* the value m such that (*this)-m*c is reduced.
                           we can assume c is nonnegative. */
    if (c.data == 0)
      return 0; /* no possible reduction */
    long m = this->data / c.data;
#ifndef MOD2
    if (this->data - m * c.data < 0)
      m--; /* C rounds to 0, not down */
#endif
    return m;
  }

