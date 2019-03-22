/****************************************************************
 * fast integers, combining signed long int and gmp ints
 * (C) 2017 Laurent Bartholdi
 ****************************************************************
 * we use the fact that pointers are word-aligned to represent an
 * integer either as an odd number or as a pointer to a mpz_t.
 ****************************************************************/

template<> class __ring0<-1U> {
  union {
    int64_t d;
    mpz_ptr p;
    bool t:1;
  };

  size_t __hashkey() {
    size_t seed = p->_mp_size;
    for (unsigned i = 0; i < abs(p->_mp_size); i++)
      seed ^= p->_mp_d[i] + 0x9e3779b9 + (seed << 6) + (seed >> 2);
    return seed;
  }
  
  void __add(const __ring0 &a, const __ring0 &b) {
    /* ideally, test if a is D, (b is P and 2b fits in long) and a+2b is OK;
       and if (a is P and 2a fits in long) and b is D and 2a+b is OK */
    if (t)
      p = new mpz_t;
    if (a.t & b.t)
      mpz_set_si(p, (a.d >> 1) + (b.d >> 1));
    else {
      if (a.t && a.d >= 0) mpz_add_ui(p, b.p, a.d >> 1);
      else if (a.t && a.d < 0) mpz_sub_ui(p, b.p, -a.d >> 1);
      else if (b.t && b.d >= 0) mpz_add_ui(p, a.p, b.d >> 1);
      else if (b.t && b.d < 0) mpz_sub_ui(p, a.p, -b.d >> 1);
      else mpz_add(p, a.p, b.p);
    }
  }

  void __mul(const __ring0 &a, const __ring0 &b) {
    if (t)
      p = new mpz_t;
    if (a.t && b.t)
      mpz_set_si(p, a.d >> 1), mpz_mul_si(p, p, b.d >> 1);
    else {
      if (a.t) mpz_mul_si(p, b.p, a.d >> 1);
      else if (b.t) mpz_mul_si(p, a.p, b.d >> 1);
      else mpz_mul(p, a.p, b.p);
    }
  }

public:
  static const char *COEFF_ID() {
    return "ℤ as union{int64_t,mpz_ptr}";
  }

  inline void init() {
    d = 1;
  }

  inline void init_set(const __ring0 &a) {
    d = 1; set(a);
  }

  inline void init_set_si(int64_t a) {
    d = 1; set_si(a);
  }

  inline void z_clear() {
    if (!t) {
      mpz_clear(p);
      delete p;
    }
  }

  inline size_t hashkey() {
    if (__builtin_expect(t, 1))
      return d;
    else
      return __hashkey();
  }

  inline bool nz_p() const {
    if (__builtin_expect(t, 1))
      return d != 1;
    else
      return mpz_sgn(p) != 0;
  }

  inline bool z_p() const { return !nz_p(); }

  inline bool reduced_p(const __ring0 &b) const {
    return b.z_p() || (sgn() >= 0 && cmp(b) == -1);
  }

  inline void set(const __ring0 &a) {
    if (__builtin_expect(t && a.t, 1))
      d = a.d;
    else if (!a.t) {
      if (t) p = new mpz_t;
      mpz_set(p, a.p);
    } else
      mpz_set_si(p, a.d >> 1);
  }

  inline void set_si(int64_t a) {
    if (__builtin_expect(t && (a ^ (a<<1)) >= 0, 1))
      d = (a << 1) | 1;
    else {
      if (t) p = new mpz_t;
      mpz_set_si(p, a);
    }
  }

  inline int64_t get_si() const {
    if (__builtin_expect(t, 1))
      return d >> 1;
    else
      return mpz_get_si(p);
  }

  inline void zero() {
    if (__builtin_expect(t, 1))
      d = 1;
    else
      mpz_set_si(p, 0);
  }
  
  inline void add(const __ring0 &a, const __ring0 &b) {
    int64_t r;
    if (__builtin_expect(t && a.t && b.t && !__builtin_saddll_overflow(a.d, b.d-1, &r), 1))
      d = r;
    else
      __add(a, b);
  }

  inline void add_si(const __ring0 &a, int64_t b) {  
  }

  inline void addmul(const __ring0 &a, const __ring0 &b) {
  }
  
  inline int cmp(const __ring0 &b) const {
    return 0;
  }

  inline int cmp_si(int64_t b) const {
    return 0;
  }

  inline void mul(const __ring0 &a, const __ring0 &b) {
  }
  
  inline void mul_si(const __ring0 &a, int64_t b) {
  }

  inline void neg(const __ring0 &a) {
  }

  inline int sgn() const {
    if (__builtin_expect(t, 1))
      return (d > 1) - (d < 1);
    else
      return mpz_sgn(p);
  }

  inline void sub(const __ring0 &a, const __ring0 &b) {
  }

  inline void submul(const __ring0 &a, const __ring0 &b) {
  }

  inline friend void gcdext(__ring0 &gcd, __ring0 &s, __ring0 &t, const __ring0 &a, const __ring0 &b) {
  }

  inline int out_str(FILE *f) const {
    return 0;
  }

  inline char *get_str(char *s, int base) const {
    return nullptr;
  }

  void swap(__ring0 &b) {
  }

#if 0
inline void print (z_t a) {
  if (a.t) {
    printf("<%ld>", a.d >> 1);
  } else {
    printf("["); mpz_out_str(stdout, 10, a.p); printf("]");
  }
}

/****************************************************************/

inline void z_abs (z_t &result, const z_t &a) {
  if (__builtin_expect(result.t && a.t && a.d != LONG_MIN, 1)) {
    result.d = abs(a.d-1) + 1;
  } else {
    if (result.t)
      mpz_init(result.p);
    if (a.t) {
      mpz_set_si(result.p, a.d >> 1);
      mpz_abs(result.p, result.p);
    } else
      mpz_abs(result.p, a.p);
  }
}

void __z_add (z_t &, const z_t &, const z_t &);
inline void z_add (z_t &result, const z_t &a, const z_t &b) {
  if (__builtin_expect(result.t && a.t && b.t && !__builtin_saddl_overflow(a.d, b.d-1, &result.d), 1))
    ;
  else
    __z_add(result, a, b);
}

inline void z_add_ui (z_t &, const z_t &, unsigned long int);
inline void z_addmul (z_t &, const z_t &, const z_t &);
inline void z_addmul_ui (z_t &, const z_t &, unsigned long int);
inline void z_and (z_t &, const z_t &, const z_t &);
inline void z_array_init (z_t &, mp_size_t, mp_size_t);
inline void z_bin_ui (z_t &, const z_t &, unsigned long int);
inline void z_bin_uiui (z_t &, unsigned long int, unsigned long int);
inline void z_cdiv_q (z_t &, const z_t &, const z_t &);
inline void z_cdiv_q_2exp (z_t &, const z_t &, mp_bitcnt_t);
inline unsigned long int z_cdiv_q_ui (z_t &, const z_t &, unsigned long int);
inline void z_cdiv_qr (z_t &, z_t &, const z_t &, const z_t &);
inline unsigned long int z_cdiv_qr_ui (z_t &, z_t &, const z_t &, unsigned long int);
inline void z_cdiv_r (z_t &, const z_t &, const z_t &);
inline void z_cdiv_r_2exp (z_t &, const z_t &, mp_bitcnt_t);
inline unsigned long int z_cdiv_r_ui (z_t &, const z_t &, unsigned long int);
inline unsigned long int z_cdiv_ui (const z_t &, unsigned long int) __GMP_ATTRIBUTE_PURE;

inline void z_clear(z_t &a) {
  if (!a.t) {
    mpz_clear(a.p);
    delete a.p;
  }
}

inline void z_clears (z_t &, ...);
inline void z_clrbit (z_t &, mp_bitcnt_t);
inline int z_cmp (const z_t &, const z_t &) __GMP_NOTHROW __GMP_ATTRIBUTE_PURE;
inline int z_cmp_d (const z_t &, double) __GMP_ATTRIBUTE_PURE;
inline int z_cmp_si (const z_t &, signed long int) __GMP_NOTHROW __GMP_ATTRIBUTE_PURE;
inline int z_cmp_ui (const z_t &, unsigned long int) __GMP_NOTHROW __GMP_ATTRIBUTE_PURE;
inline int z_cmpabs (const z_t &, const z_t &) __GMP_NOTHROW __GMP_ATTRIBUTE_PURE;
inline int z_cmpabs_d (const z_t &, double) __GMP_ATTRIBUTE_PURE;
inline int z_cmpabs_ui (const z_t &, unsigned long int) __GMP_NOTHROW __GMP_ATTRIBUTE_PURE;
inline void z_com (z_t &, const z_t &);
inline void z_combit (z_t &, mp_bitcnt_t);
inline int z_congruent_p (const z_t &, const z_t &, const z_t &) __GMP_ATTRIBUTE_PURE;
inline int z_congruent_2exp_p (const z_t &, const z_t &, mp_bitcnt_t) __GMP_NOTHROW __GMP_ATTRIBUTE_PURE;
inline int z_congruent_ui_p (const z_t &, unsigned long, unsigned long) __GMP_ATTRIBUTE_PURE;
inline void z_divexact (z_t &, const z_t &, const z_t &);
inline void z_divexact_ui (z_t &, const z_t &, unsigned long);
inline int z_divisible_p (const z_t &, const z_t &) __GMP_ATTRIBUTE_PURE;
inline int z_divisible_ui_p (const z_t &, unsigned long) __GMP_ATTRIBUTE_PURE;
inline int z_divisible_2exp_p (const z_t &, mp_bitcnt_t) __GMP_NOTHROW __GMP_ATTRIBUTE_PURE;
inline void z_dump (const z_t &);
inline void *z_export (void *, size_t *, int, size_t, int, size_t, const z_t &);
inline void z_fac_ui (z_t &, unsigned long int);
inline void z_2fac_ui (z_t &, unsigned long int);
inline void z_mfac_uiui (z_t &, unsigned long int, unsigned long int);
inline void z_primorial_ui (z_t &, unsigned long int);
inline void z_fdiv_q (z_t &, const z_t &, const z_t &);
inline void z_fdiv_q_2exp (z_t &, const z_t &, mp_bitcnt_t);
inline unsigned long int z_fdiv_q_ui (z_t &, const z_t &, unsigned long int);
inline void z_fdiv_qr (z_t &, z_t &, const z_t &, const z_t &);
inline unsigned long int z_fdiv_qr_ui (z_t &, z_t &, const z_t &, unsigned long int);
inline void z_fdiv_r (z_t &, const z_t &, const z_t &);
inline void z_fdiv_r_2exp (z_t &, const z_t &, mp_bitcnt_t);
inline unsigned long int z_fdiv_r_ui (z_t &, const z_t &, unsigned long int);
inline unsigned long int z_fdiv_ui (const z_t &, unsigned long int) __GMP_ATTRIBUTE_PURE;
inline void z_fib_ui (z_t &, unsigned long int);
inline void z_fib2_ui (z_t &, z_t &, unsigned long int);
inline int z_fits_sint_p (const z_t &) __GMP_NOTHROW __GMP_ATTRIBUTE_PURE;
inline int z_fits_slong_p (const z_t &) __GMP_NOTHROW __GMP_ATTRIBUTE_PURE;
inline int z_fits_sshort_p (const z_t &) __GMP_NOTHROW __GMP_ATTRIBUTE_PURE;
inline int z_fits_uint_p (const z_t &) __GMP_NOTHROW __GMP_ATTRIBUTE_PURE;
inline int z_fits_ulong_p (const z_t &) __GMP_NOTHROW __GMP_ATTRIBUTE_PURE;
inline int z_fits_ushort_p (const z_t &) __GMP_NOTHROW __GMP_ATTRIBUTE_PURE;
inline void z_gcd (z_t &, const z_t &, const z_t &);
inline unsigned long int z_gcd_ui (z_t &, const z_t &, unsigned long int);
inline void z_gcdext (z_t &, z_t &, z_t &, const z_t &, const z_t &);
inline double z_get_d (const z_t &) __GMP_ATTRIBUTE_PURE;
inline double z_get_d_2exp (signed long int *, const z_t &);

inline long z_get_si(const z_t &a) {
  if (a.t)
    return a.d >> 1;
  if (mpz_fits_slong_p(a.p))
    return mpz_get_si(a.p);
  throw("z_get_si(): cannot fit in a signed long");
}

inline char *z_get_str (char *, int, const z_t &);
inline unsigned long int z_get_ui (const z_t &) __GMP_NOTHROW __GMP_ATTRIBUTE_PURE;
inline mp_bitcnt_t z_hamdist (const z_t &, const z_t &) __GMP_NOTHROW __GMP_ATTRIBUTE_PURE;
inline void z_import (z_t &, size_t, int, size_t, int, size_t, const void *);

inline void z_init(z_t &a) {
  a.d = 1;
}

inline void z_init2 (z_t &, mp_bitcnt_t);
inline void z_inits (z_t &, ...);
inline void z_init_set (z_t &, const z_t &);
inline void z_init_set_d (z_t &, double);

inline void z_init_set_si (z_t &result, signed long int s) {
  if (__builtin_expect(__builtin_add_overflow(s, s, &result.d), 0))
    result.t = 1;
  else {
    result.p = new mpz_t;
    mpz_init_set_si(result.p, s);
  }
}

inline int z_init_set_str (z_t &, const char *, int);
inline void z_init_set_ui (z_t &, unsigned long int);
inline size_t z_inp_raw (z_t &, FILE *);
inline size_t z_inp_str (z_t &, FILE *, int);
inline int z_invert (z_t &, const z_t &, const z_t &);
inline void z_ior (z_t &, const z_t &, const z_t &);
inline int z_jacobi (const z_t &, const z_t &) __GMP_ATTRIBUTE_PURE;
inline int z_kronecker_si (const z_t &, long) __GMP_ATTRIBUTE_PURE;
inline int z_kronecker_ui (const z_t &, unsigned long) __GMP_ATTRIBUTE_PURE;
inline int z_si_kronecker (long, const z_t &) __GMP_ATTRIBUTE_PURE;
inline int z_ui_kronecker (unsigned long, const z_t &) __GMP_ATTRIBUTE_PURE;
inline void z_lcm (z_t &, const z_t &, const z_t &);
inline void z_lcm_ui (z_t &, const z_t &, unsigned long);
inline void z_lucnum_ui (z_t &, unsigned long int);
inline void z_lucnum2_ui (z_t &, z_t &, unsigned long int);
inline int z_millerrabin (const z_t &, int) __GMP_ATTRIBUTE_PURE;
inline void z_mod (z_t &, const z_t &, const z_t &);

void __z_mul(z_t &, const z_t &, const z_t &);
inline void z_mul(z_t &result, const z_t &a, const z_t &b) {
  if (__builtin_expect(result.t && a.t && b.t && !__builtin_smull_overflow(a.d >> 1, b.d-1, &result.d), 1))
    result.t = 1;
  else
    __z_mul(result, a, b);
}

inline void z_mul_2exp (z_t &, const z_t &, mp_bitcnt_t);
inline void z_mul_si (z_t &, const z_t &, long int);
inline void z_mul_ui (z_t &, const z_t &, unsigned long int);
inline void z_neg (z_t &, const z_t &);
inline void z_nextprime (z_t &, const z_t &);
inline size_t z_out_raw (FILE *, const z_t &);
inline size_t z_out_str (FILE *, int, const z_t &);
inline int z_perfect_power_p (const z_t &) __GMP_ATTRIBUTE_PURE;
inline int z_perfect_square_p (const z_t &) __GMP_ATTRIBUTE_PURE;
inline mp_bitcnt_t z_popcount (const z_t &) __GMP_NOTHROW __GMP_ATTRIBUTE_PURE;
inline void z_pow_ui (z_t &, const z_t &, unsigned long int);
inline void z_powm (z_t &, const z_t &, const z_t &, const z_t &);
inline void z_powm_sec (z_t &, const z_t &, const z_t &, const z_t &);
inline void z_powm_ui (z_t &, const z_t &, unsigned long int, const z_t &);
inline int z_probab_prime_p (const z_t &, int) __GMP_ATTRIBUTE_PURE;
inline void z_random (z_t &, mp_size_t);
inline void z_random2 (z_t &, mp_size_t);
inline void z_realloc2 (z_t &, mp_bitcnt_t);
inline mp_bitcnt_t z_remove (z_t &, const z_t &, const z_t &);
inline int z_root (z_t &, const z_t &, unsigned long int);
inline void z_rootrem (z_t &, z_t &, const z_t &, unsigned long int);
inline void z_rrandomb (z_t &, gmp_randstate_t, mp_bitcnt_t);
inline mp_bitcnt_t z_scan0 (const z_t &, mp_bitcnt_t) __GMP_NOTHROW __GMP_ATTRIBUTE_PURE;
inline mp_bitcnt_t z_scan1 (const z_t &, mp_bitcnt_t) __GMP_NOTHROW __GMP_ATTRIBUTE_PURE;
inline void z_set (z_t &, const z_t &);
inline void z_set_d (z_t &, double);
inline void z_set_f (z_t &, mpf_srcptr);
inline void z_set_q (z_t &, mpq_srcptr);
inline void z_set_si (z_t &, signed long int);
inline int z_set_str (z_t &, const char *, int);
inline void z_set_ui (z_t &, unsigned long int);
inline void z_setbit (z_t &, mp_bitcnt_t);
inline size_t z_size (const z_t &) __GMP_NOTHROW __GMP_ATTRIBUTE_PURE;
inline size_t z_sizeinbase (const z_t &, int) __GMP_NOTHROW __GMP_ATTRIBUTE_PURE;
inline void z_sqrt (z_t &, const z_t &);
inline void z_sqrtrem (z_t &, z_t &, const z_t &);
inline void z_sub (z_t &, const z_t &, const z_t &);
inline void z_sub_ui (z_t &, const z_t &, unsigned long int);
inline void z_ui_sub (z_t &, unsigned long int, const z_t &);
inline void z_submul (z_t &, const z_t &, const z_t &);
inline void z_submul_ui (z_t &, const z_t &, unsigned long int);
inline void z_swap (z_t &, z_t &) __GMP_NOTHROW;
inline unsigned long int z_tdiv_ui (const z_t &, unsigned long int) __GMP_ATTRIBUTE_PURE;
inline void z_tdiv_q (z_t &, const z_t &, const z_t &);
inline void z_tdiv_q_2exp (z_t &, const z_t &, mp_bitcnt_t);
inline unsigned long int z_tdiv_q_ui (z_t &, const z_t &, unsigned long int);
inline void z_tdiv_qr (z_t &, z_t &, const z_t &, const z_t &);
inline unsigned long int z_tdiv_qr_ui (z_t &, z_t &, const z_t &, unsigned long int);
inline void z_tdiv_r (z_t &, const z_t &, const z_t &);
inline void z_tdiv_r_2exp (z_t &, const z_t &, mp_bitcnt_t);
inline unsigned long int z_tdiv_r_ui (z_t &, const z_t &, unsigned long int);
inline int z_tstbit (const z_t &, mp_bitcnt_t) __GMP_NOTHROW __GMP_ATTRIBUTE_PURE;
inline void z_ui_pow_ui (z_t &, unsigned long int, unsigned long int);
inline void z_urandomb (z_t &, gmp_randstate_t, mp_bitcnt_t);
inline void z_urandomm (z_t &, gmp_randstate_t, const z_t &);
inline void z_xor (z_t &, const z_t &, const z_t &);
inline std::ostream& operator<< (std::ostream &, const z_t &);
inline std::istream& operator>> (std::istream &, z_t &);

#endif

  // conversions
  template<unsigned L> friend class __ring0;
  template<uint64_t Q, unsigned L> friend class __localp_small;
  template<uint64_t Q, unsigned L> friend class __localp_big;
  template<unsigned L> friend class __local2_small;
  template<unsigned L> friend class __local2_big;
  
  template<uint64_t Q, unsigned L> void map(const __localp_big<Q,L> &a) {
    set_si(a.data[0]);
  }

};
