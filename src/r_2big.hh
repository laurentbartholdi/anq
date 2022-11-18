template<unsigned K> class __local2_big {
  static const unsigned COEFF_WORDS = (K + GMP_LIMB_BITS - 1) / GMP_LIMB_BITS;
  static const mp_limb_t COEFF_MASK = (K % GMP_LIMB_BITS == 0) ? ~0LL : ((1ULL << (K % GMP_LIMB_BITS)) - 1);

  mp_limb_t data[COEFF_WORDS];

  struct doubleword {
    mp_limb_t data[2*COEFF_WORDS];
  };

  inline static unsigned __nzlimbs(const mp_limb_t *a, unsigned na) {
    while (na > 0 && a[na-1] == 0) na--;
    return na;
  }

  static void __rshift(mp_limb_t *result, const mp_limb_t *a, unsigned shift) {
    unsigned shift0 = shift/GMP_LIMB_BITS, shift1 = shift%GMP_LIMB_BITS;
    
    if (shift1)
      mpn_rshift(result, a + shift0, COEFF_WORDS - shift0, shift1);
    else
      mpn_copyi(result, a + shift0, COEFF_WORDS - shift0);
    for (unsigned i = COEFF_WORDS-shift0; i < COEFF_WORDS; i++)
      result[i] = 0;
  }
  
  inline static void __singlebit(__local2_big &a, unsigned shift) {
    a.zero();
    a.data[shift / GMP_LIMB_BITS] = 1ULL << (shift % GMP_LIMB_BITS);
  }

  inline void inverse_mod_2_k(const __local2_big &a, unsigned shift) {
    __local2_big shifteda;

    shifteda.zero();
    __rshift(shifteda.data, a.data, shift);

    set(shifteda); // already 3 correct bits
    for (unsigned i = 3; i < K; i <<= 1) {
      // result *= 2-shifteda*result
      doubleword temp, temp2;
      mpn_mul_n(temp.data, shifteda.data, data, COEFF_WORDS);
      mpn_sub_1(temp2.data, temp.data, COEFF_WORDS, 2);
      mpn_neg(temp.data, temp2.data, COEFF_WORDS);
      mpn_mul_n(temp2.data, data, temp.data, COEFF_WORDS);
      mpn_copyi(data, temp2.data, COEFF_WORDS);
    }
    data[COEFF_WORDS-1] &= COEFF_MASK;
  }

public:
  static const char *COEFF_ID() {
    static char s[100];
    snprintf(s, 100, "ℤ/2^%u as mp_limb_t[%u]", K, COEFF_WORDS);
    return s;
  }

  inline size_t hashkey() const {
    size_t seed = COEFF_WORDS;
    for (unsigned i = 0; i < COEFF_WORDS; i++)
      seed ^= data[i] + 0x9e3779b9 + (seed << 6) + (seed >> 2);
    return seed;
  }
  
  inline bool z_p() const {
    return mpn_zero_p(data, COEFF_WORDS);
  }

  inline bool nz_p() const { return !z_p(); }

  /* returns true if a in [0,b) or b=0 */
  inline bool reduced_p(const __local2_big &b) const {
    return b.z_p() || cmp(b) < 0;
  }
  
  inline void set(const __local2_big &a) {
    mpn_copyi(data, a.data, COEFF_WORDS);
  }

  inline void set_si(int64_t a) {
    zero();
    if (a >= 0)
      data[0] = a;
    else {
      data[0] = -a;
      mpn_neg(data, data, COEFF_WORDS);
      data[COEFF_WORDS-1] &= COEFF_MASK;
    }
  }

  inline int64_t get_si() const {
    int64_t r = data[0];
    if (r >= 0) {
      for (unsigned i = 1; i < COEFF_WORDS; i++)
	if (data[i] != 0)
	  goto error;
      return r;
    } else {
      for (unsigned i = 1; i < COEFF_WORDS-1; i++)
	if (data[i] != (uint64_t) -1)
	  goto error;
      if (data[COEFF_WORDS-1] != COEFF_MASK)
	goto error;
      return r;
    }
  error:
    throw std::runtime_error("get_si(): data cannot fit in an int64_t");
  }

  inline void zero() { mpn_zero(data, COEFF_WORDS); }

  inline void add(const __local2_big &a, const __local2_big &b) {
    mpn_add_n(data, a.data, b.data, COEFF_WORDS);
    data[COEFF_WORDS-1] &= COEFF_MASK;
  }

  inline void add_si(const __local2_big &a, int64_t b) {
    if (b >= 0)
      mpn_add_1(data, a.data, COEFF_WORDS, b);
    else
      mpn_sub_1(data, a.data, COEFF_WORDS, -b);
    data[COEFF_WORDS-1] &= COEFF_MASK;
  }
  
  inline void addmul(const __local2_big &a, const __local2_big &b) {
    doubleword temp;
    mpn_mul_n(temp.data, a.data, b.data, COEFF_WORDS);
    mpn_add_n(data, data, temp.data, COEFF_WORDS);
    data[COEFF_WORDS-1] &= COEFF_MASK;
  }

  inline int cmp(const __local2_big &b) const {
    return mpn_cmp(data, b.data, COEFF_WORDS);
  }

  /* I don't know how to implement a meaningful compare on residue classes. Let's return 0 or 1 */
  inline int cmp_si(int64_t b) const {
    if (b >= 0)
      return data[0] != (unsigned long) b || !mpn_zero_p(data+1, COEFF_WORDS-1);
    else {
      __local2_big c;
      mpn_add_1(c.data, data, COEFF_WORDS, -b);
      c.data[COEFF_WORDS-1] &= COEFF_MASK;
      return c.nz_p();
    }
  }

  inline friend void fdiv_qr(__local2_big &q, __local2_big &r, const __local2_big &a, const __local2_big &b) {
    __local2_big __b, __r;
    unsigned i;
    for (i = 0; b.data[i] == 0; i++)
      __r.data[i] = a.data[i];
    __r.data[i] = a.data[i] & ((b.data[i] & -b.data[i]) - 1);
    for (++i; i < COEFF_WORDS; i++)
      __r.data[i] = 0;
    unsigned shift = mpn_scan1(b.data, 0);
    __rshift(__b.data, b.data, shift);
    __rshift(q.data, a.data, shift);
    __b.inv(__b);
    q.mul(q, __b);
    r.set(__r);
  }

  inline friend uint64_t fdiv_qr_ui(__local2_big &q, __local2_big &r, const __local2_big &a, uint64_t b) {
    __local2_big __b;
    __b.data[0] = b; mpn_zero(__b.data+1, COEFF_WORDS-1);
    fdiv_qr(q, r, a, __b);
    return r.data[0];
  }

  inline friend void shdiv_qr(__local2_big &q, __local2_big &r, const __local2_big &a, const __local2_big &b) {
    __local2_big __r;
    unsigned i;
    for (i = 0; b.data[i] == 0; i++)
      __r.data[i] = a.data[i];
    __r.data[i] = a.data[i] & (b.data[i] - 1);
    for (++i; i < COEFF_WORDS; i++)
      __r.data[i] = 0;
    __rshift(q.data, a.data, mpn_scan1(b.data, 0));
    r.set(__r);
  }

  inline friend uint64_t shdiv_qr_ui(__local2_big &q, __local2_big &r, const __local2_big &a, uint64_t b) {
    uint64_t __r = a.data[0] & ((b & -b) - 1);
    __rshift(q.data, a.data, __builtin_ctzll(b));
    r.data[0] = __r; mpn_zero(r.data+1, COEFF_WORDS-1);
    return __r;
  }

  inline void inv(const __local2_big &a) {
    unsigned aval = a.z_p() ? -1 : mpn_scan1(a.data, 0);
    if (aval != 0)
      throw std::runtime_error("inv() of non-invertible element");
    else
      inverse_mod_2_k(a, 0);
  }

  inline void mul(const __local2_big &a, const __local2_big &b) {
    doubleword temp;
    mpn_mul_n(temp.data, a.data, b.data, COEFF_WORDS);
    mpn_copyi(data, temp.data, COEFF_WORDS);
    data[COEFF_WORDS-1] &= COEFF_MASK;
  }

  inline void mul_si(const __local2_big &a, int64_t b) {
    if (b >= 0)
      mpn_mul_1(data, a.data, COEFF_WORDS, b);
    else {
      mpn_mul_1(data, a.data, COEFF_WORDS, -b);
      mpn_neg(data, data, COEFF_WORDS);
    }
    data[COEFF_WORDS-1] &= COEFF_MASK;
  }

  inline void neg(const __local2_big &a) {
    mpn_neg(data, a.data, COEFF_WORDS);
    data[COEFF_WORDS-1] &= COEFF_MASK;
  }

  inline int sgn() const {
    return nz_p();
  }

  inline void sub(const __local2_big &a, const __local2_big &b) {
    mpn_sub_n(data, a.data, b.data, COEFF_WORDS);
    data[COEFF_WORDS-1] &= COEFF_MASK;
  }

  inline void submul(const __local2_big &a, const __local2_big &b) {
    doubleword temp;
    mpn_mul_n(temp.data, a.data, b.data, COEFF_WORDS);
    mpn_sub_n(data, data, temp.data, COEFF_WORDS);
    data[COEFF_WORDS-1] &= COEFF_MASK;
  }

  inline unsigned val(const __local2_big &a) {
    if (a.z_p()) {
      zero();
      return UINT_MAX;
    }

    unsigned aval = mpn_scan1(a.data, 0);
    __rshift(data, a.data, aval);
    return aval;
  }

  inline friend void gcdext(__local2_big &gcd, __local2_big &s, __local2_big &t, const __local2_big &a, const __local2_big &b) {
    unsigned aval = a.z_p() ? -1 : mpn_scan1(a.data, 0),
      bval = mpn_scan1(b.data, 0);

    if (aval >= bval) {
      __singlebit(gcd, bval);
      mpn_zero(s.data, COEFF_WORDS);
      t.inverse_mod_2_k(b, bval);
    } else {
      __singlebit(gcd, aval);
      s.inverse_mod_2_k(a, aval);
      mpn_zero(t.data, COEFF_WORDS);
    }
  }

  /* returns unit and generator of annihilator ideal:
     a*unit is canonical (2^n) and a*annihilator=0 */
  inline friend void unit_annihilator(__local2_big *unit, __local2_big *annihilator, const __local2_big &a) {
    if (a.z_p()) {
      if (unit) unit->zero();
      if (annihilator) annihilator->set_si(1);
      return;
    }
    unsigned shift = mpn_scan1(a.data, 0);
    if (unit) unit->inverse_mod_2_k(a, shift);
    if (annihilator) {
      if (shift > 0)
	__singlebit(*annihilator, K - shift);
      else
	mpn_zero(annihilator->data, COEFF_WORDS);
    }
  }

  inline char *get_str(char *s, int len, int base) const {
    char *p;

    mp_limb_t temp[COEFF_WORDS];
    mpn_copyi(temp, data, COEFF_WORDS);
    int sign =
#ifdef PRINT_2SIGNED
      (temp[COEFF_WORDS-1] > COEFF_MASK >> 1);
#else
    0;
#endif
    if (sign) {
      mpn_neg(temp, temp, COEFF_WORDS);
      temp[COEFF_WORDS-1] &= COEFF_MASK;
    }
    unsigned nzlimbs = __nzlimbs(temp, COEFF_WORDS);
    size_t digits = mpn_sizeinbase(temp, nzlimbs, 10);

    if (len == 0)
      len = digits+1+sign;
    
    if (s == nullptr)
      p = (char *) malloc(len);
    else
      p = s;

    if (sign)
      p[0] = '-';

    digits = mpn_get_str((unsigned char *) p+sign, base, temp, nzlimbs);
    for (unsigned i = 0; i < digits; i++)
      p[i+sign] += '0';
    p[digits+sign] = 0;

    if (s == nullptr)
      p = (char *) realloc(p, digits+1+sign);

    return p;
  }

  inline int out_str(FILE *f) const {
    char *s = (char *) get_str(nullptr, 0, 10);
    fprintf(f, "%s", s); /* maybe we should print in base characteristic? */
    int digits = strlen(s);
    free(s);
  
    return digits;
  }

  // conversions
  template<unsigned L> friend class __ring0;
  //template<uint64_t Q, unsigned L> friend class __localp_small;
  //template<uint64_t Q, unsigned L> friend class __localp_big;
  template<unsigned L> friend class __local2_small;
  template<unsigned L> friend class __local2_big;

  template<unsigned L> inline void map(const __ring0<L> &a) {
    if (a.period()) {
      __ring0<L> b;
      b.neg(a);
      map(b);
      neg(*this);
    } else {
      if (COEFF_WORDS > L) {
	zero();
	mpn_copyi(data, a.data, L);
      } else {
	mpn_copyi(data, a.data, COEFF_WORDS);
	data[COEFF_WORDS-1] &= COEFF_MASK;
      }
    }
  }

  inline void map(const __ring0_mpz &a) {
    mp_size_t L = a.data[0]._mp_size;
    bool sign = L < 0;
    if (sign) L = -L;
    if (COEFF_WORDS > L) {
      zero();
      mpn_copyi(data, a.data[0]._mp_d, L);
    } else {
      mpn_copyi(data, a.data[0]._mp_d, COEFF_WORDS);
      data[COEFF_WORDS-1] &= COEFF_MASK;
    }
    if (sign)
      neg(*this);
  }

  inline void map(const __ring0_64 &a) {
    zero();
    if (a.data >= 0)
      data[0] = a.data;
    else {
      data[0] = -a.data;
      neg(*this);
    }
  }

  template<unsigned L> inline void map(const __local2_big<L> &a) {
    if (K == L)
      mpn_copyi(data, a.data, a.COEFF_WORDS);
    else if (K > L) {
      zero();
      mpn_copyi(data, a.data, a.COEFF_WORDS);
    } else {
      mpn_copyi(data, a.data, COEFF_WORDS);
      data[COEFF_WORDS-1] &= COEFF_MASK;
    }
  }
  
  template<unsigned L> inline void map(const __local2_small<L> &a) {
    zero();
    data[0] = a.data;
  }
};
