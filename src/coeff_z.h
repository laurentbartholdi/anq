/****************************************************************
 * z.h
 * fast integers, combining signed long int and gmp ints
 * (C) 2017 Laurent Bartholdi
 ****************************************************************
 * we use the fact that pointers are word-aligned to represent an
 * integer either as an odd number or as a pointer to a mpz_t.
 ****************************************************************/

#include <stdio.h>
#include <gmp.h>

union z_t {
  signed long d;
  mpz_ptr p;
  bool t:1;
  z_t() = default;
  z_t(long s) {
    if (__builtin_add_overflow(s, s, &d)) {
      p = new mpz_t;
      mpz_init_set_si(p, s);
    } else
      d |= 1;
  }
};

inline void z_init(z_t &a) {
  a.d = 1;
}

inline void z_clear(z_t &a) {
  if (!(a.d & 1)) {
    fprintf(stderr,"(free %p)",a.p);
    mpz_clear(a.p);
    delete a.p;
  }
}

void print(z_t a) {
  if (a.d & 1) {
    printf("<%ld>", a.d >> 1);
  } else {
    printf("["); mpz_out_str(stdout, 10, a.p); printf("]");
  }
}


long z_get_si(z_t &a) {
  if (a.d & 1)
    return a.d >> 1;
  if (mpz_fits_slong_p(a.p))
    return mpz_get_si(a.p);
  throw("z_get_si(): cannot fit in a signed long");
}

inline z_t operator +(const z_t &a, const z_t &b) {
  z_t result;
  
  if (!(a.d & b.d & 1) || __builtin_saddl_overflow(a.d, b.d-1, &result.d)) {
    /* ideally, test if a is D, (b is P and 2b fits in long) and a+2b is OK;
       and if (a is P and 2a fits in long) and b is D and 2a+b is OK */
    result.p = new mpz_t;
    if (a.d & b.d & 1)
      mpz_init_set_si(result.p, (a.d >> 1) + (b.d >> 1));
    else {
      mpz_init(result.p);
      if ((a.d & 1) && a.d >= 0) mpz_add_ui(result.p, b.p, a.d >> 1);
      else if ((a.d & 1) && a.d < 0) mpz_sub_ui(result.p, b.p, -a.d >> 1);
      else if ((b.d & 1) && b.d >= 0) mpz_add_ui(result.p, a.p, b.d >> 1);
      else if ((b.d & 1) && b.d < 0) mpz_sub_ui(result.p, a.p, -b.d >> 1);
      else mpz_add(result.p, a.p, b.p);
    }
  }
  return result;
}

inline z_t operator *(const z_t &a, const z_t &b) {
  z_t result;
  
  if (!(a.d & b.d & 1) || __builtin_smull_overflow(a.d >> 1, b.d-1, &result.d)) {
    result.p = new mpz_t;
    if (a.d & b.d & 1)
      mpz_init_set_si(result.p, a.d >> 1), mpz_mul_si(result.p, result.p, b.d >> 1);
    else {
      mpz_init(result.p);
      if (a.d & 1) mpz_mul_si(result.p, b.p, a.d >> 1);
      else if (b.d & 1) mpz_mul_si(result.p, a.p, b.d >> 1);
      else mpz_mul(result.p, a.p, b.p);
    }
  } else
    result.d |= 1;
  return result;
}
