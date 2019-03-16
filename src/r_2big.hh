template<unsigned K> class local2_big {
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

  inline static void __singlebit(local2_big &a, unsigned shift) {
    a.zero();
    a.data[shift / GMP_LIMB_BITS] = 1ULL << (shift % GMP_LIMB_BITS);
  }

  inline void inverse_mod_2_k(const local2_big &a, unsigned shift) {
    local2_big shifteda;

    shifteda.zero();
    mpn_rshift(shifteda.data, a.data + shift/GMP_LIMB_BITS, COEFF_WORDS - shift/GMP_LIMB_BITS, shift%GMP_LIMB_BITS);

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
    sprintf(s, "ℤ/2^%u as mp_limb_t[%u]", K, COEFF_WORDS);
    return s;
  }

  inline size_t hash() const {
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
  inline bool reduced_p(const local2_big &b) const {
    return b.z_p() || cmp(b) < 0;
  }
  
  inline void set(const local2_big &a) {
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
    if (r > 0) {
      for (unsigned i = 1; i < COEFF_WORDS; i++)
	if (data[i] != 0)
	  goto error;
      return r;
    } else {
      for (unsigned i = 1; i < COEFF_WORDS-1; i++)
	if (data[i] != -1)
	  goto error;
      if (data[COEFF_WORDS-1] != COEFF_MASK)
	goto error;
      return r;
    }
  error:
    throw std::runtime_error("get_si(): data cannot fit in an int64_t");
  }

  inline void zero() { mpn_zero(data, COEFF_WORDS); }

  inline void add(const local2_big &a, const local2_big &b) {
    mpn_add_n(data, a.data, b.data, COEFF_WORDS);
    data[COEFF_WORDS-1] &= COEFF_MASK;
  }

  inline void add_si(const local2_big &a, int64_t b) {
    if (b >= 0)
      mpn_add_1(data, a.data, COEFF_WORDS, b);
    else
      mpn_sub_1(data, a.data, COEFF_WORDS, -b);
    data[COEFF_WORDS-1] &= COEFF_MASK;
  }
  
  inline void addmul(const local2_big &a, const local2_big &b) {
    doubleword temp;
    mpn_mul_n(temp.data, a.data, b.data, COEFF_WORDS);
    mpn_add_n(data, data, temp.data, COEFF_WORDS);
    data[COEFF_WORDS-1] &= COEFF_MASK;
  }

  inline int cmp(const local2_big &b) const {
    return mpn_cmp(data, b.data, COEFF_WORDS);
  }

  /* I don't know how to implement a meaningful compare on residue classes. Let's return 0 or 1 */
  inline int cmp_si(int64_t b) const {
    if (b >= 0)
      return data[0] != (unsigned long) b || !mpn_zero_p(data+1, COEFF_WORDS-1);
    else {
      local2_big c;
      mpn_add_1(c.data, data, COEFF_WORDS, -b);
      c.data[COEFF_WORDS-1] &= COEFF_MASK;
      return c.nz_p();
    }
  }

  inline friend void fdiv_qr(local2_big &q, local2_big &r, const local2_big &a, const local2_big &b) {
    local2_big __b, __r;
    unsigned i;
    for (i = 0; b.data[i] == 0; i++)
      __r.data[i] = a.data[i];
    __r.data[i] = a.data[i] & ((b.data[i] & -b.data[i]) - 1);
    for (++i; i < COEFF_WORDS; i++)
      __r.data[i] = 0;
    mpn_rshift(__b.data, b.data, COEFF_WORDS, mpn_scan1(b.data, 0));
    mpn_rshift(q.data, a.data, COEFF_WORDS, mpn_scan1(b.data, 0));
    __b.inv(__b);
    q.mul(q, __b);
    r.set(__r);
  }

  inline friend uint64_t fdiv_qr_ui(local2_big &q, local2_big &r, const local2_big &a, uint64_t b) {
    local2_big __b;
    __b.data[0] = b; mpn_zero(__b.data+1, COEFF_WORDS-1);
    fdiv_qr(q, r, a, __b);
    return r.data[0];
  }

  inline friend void shdiv_qr(local2_big &q, local2_big &r, const local2_big &a, const local2_big &b) {
    local2_big __r;
    unsigned i;
    for (i = 0; b.data[i] == 0; i++)
      __r.data[i] = a.data[i];
    __r.data[i] = a.data[i] & (b.data[i] - 1);
    for (++i; i < COEFF_WORDS; i++)
      __r.data[i] = 0;
    mpn_rshift(q.data, a.data, COEFF_WORDS, mpn_scan1(b.data, 0));
    r.set(__r);
  }

  inline friend uint64_t shdiv_qr_ui(local2_big &q, local2_big &r, const local2_big &a, uint64_t b) {
    uint64_t __r = a.data[0] & ((b & -b) - 1);
    mpn_rshift(q.data, a.data, COEFF_WORDS, __builtin_ctzll(b));
    r.data[0] = __r; mpn_zero(r.data+1, COEFF_WORDS-1);
    return __r;
  }

  inline void inv(const local2_big &a) {
    unsigned aval = a.z_p() ? -1 : mpn_scan1(a.data, 0);
    if (aval != 0)
      throw std::runtime_error("inv() of non-invertible element");
    else
      inverse_mod_2_k(a, 0);
  }

  inline void mul(const local2_big &a, const local2_big &b) {
    doubleword temp;
    mpn_mul_n(temp.data, a.data, b.data, COEFF_WORDS);
    mpn_copyi(data, temp.data, COEFF_WORDS);
    data[COEFF_WORDS-1] &= COEFF_MASK;
  }

  inline void mul_si(const local2_big &a, int64_t b) {
    if (b >= 0)
      mpn_mul_1(data, a.data, COEFF_WORDS, b);
    else {
      mpn_mul_1(data, a.data, COEFF_WORDS, -b);
      mpn_neg(data, data, COEFF_WORDS);
    }
    data[COEFF_WORDS-1] &= COEFF_MASK;
  }

  inline void neg(const local2_big &a) {
    mpn_neg(data, a.data, COEFF_WORDS);
    data[COEFF_WORDS-1] &= COEFF_MASK;
  }

  inline int sgn() const {
    return nz_p();
  }

  inline void sub(const local2_big &a, const local2_big &b) {
    mpn_sub_n(data, a.data, b.data, COEFF_WORDS);
    data[COEFF_WORDS-1] &= COEFF_MASK;
  }

  inline void submul(const local2_big &a, const local2_big &b) {
    doubleword temp;
    mpn_mul_n(temp.data, a.data, b.data, COEFF_WORDS);
    mpn_sub_n(data, data, temp.data, COEFF_WORDS);
    data[COEFF_WORDS-1] &= COEFF_MASK;
  }

  inline unsigned val(const local2_big &a) {
    if (a.z_p()) {
      zero();
      return UINT_MAX;
    }

    unsigned aval = mpn_scan1(a.data, 0);
    mpn_rshift(data, a.data, COEFF_WORDS, aval);
    return aval;
  }

  inline friend void gcdext(local2_big &gcd, local2_big &s, local2_big &t, const local2_big &a, const local2_big &b) {
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
  inline friend void unit_annihilator(local2_big &unit, local2_big &annihilator, const local2_big &a) {
    if (a.z_p()) {
      unit.zero();
      annihilator.set_si(1);
      return;
    }
    unsigned shift = mpn_scan1(a.data, 0);
    unit.inverse_mod_2_k(a, shift);
    if (shift > 0)
      __singlebit(annihilator, K - shift);
    else
      mpn_zero(annihilator.data, COEFF_WORDS);
  }

  inline char *get_str(char *s, int base) const {
    char *p;

    mp_limb_t temp[COEFF_WORDS];
    mpn_copyi(temp, data, COEFF_WORDS);
    unsigned nzlimbs = __nzlimbs(temp, COEFF_WORDS);
    size_t digits = mpn_sizeinbase(temp, nzlimbs, 10);

    if (s == nullptr)
      p = (char *) malloc(digits+1);
    else
      p = s;

    digits = mpn_get_str((unsigned char *) p, base, temp, nzlimbs);
    for (unsigned i = 0; i < digits; i++)
      p[i] += '0';
    p[digits] = 0;

    if (s == nullptr)
      p = (char *) realloc(p, digits+1);

    return p;
  }

  inline int out_str(FILE *f) const {
    char *s = (char *) get_str(nullptr, 10);
    fprintf(f, "%s", s); /* maybe we should print in base characteristic? */
    int digits = strlen(s);
    free(s);
  
    return digits;
  }

  /* conversions */
};
