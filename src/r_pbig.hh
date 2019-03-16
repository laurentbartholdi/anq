#if !defined(AVOID_MPN_DIVEXACT) && !defined(mpn_divexact) // internal to gmp >= 6, probably not portable
#define mpn_divexact __gmpn_divexact
extern "C" void mpn_divexact (mp_ptr, mp_srcptr, mp_size_t, mp_srcptr, mp_size_t);
#endif

template<uint64_t P, unsigned K> class localp_big {
  static const unsigned COEFF_WORDS = (K + MAXK(P) - 1) / MAXK(P);

  mp_limb_t data[COEFF_WORDS];

  struct doubleword {
    mp_limb_t data[2*COEFF_WORDS];
  };

  inline static unsigned __nzlimbs(const mp_limb_t *a, unsigned na) {
    while (na > 0 && a[na-1] == 0) na--;
    return na;
  }

  static inline localp_big __mpn_ui(uint64_t i) {
    localp_big c;
    mpn_zero(c.data+1, c.COEFF_WORDS-1);
    c.data[0] = i;
    return c;
  }

  static inline localp_big __mpn_pow_ui(localp_big x, unsigned p) {
    localp_big c = __mpn_ui(1);
    while (p) {
      doubleword temp;
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
  
  static constexpr unsigned lgint64(uint64_t n) {
    return n ? 1+lgint64(n/2) : -1;
  }

  static const localp_big COEFF_N;

#if 0 // Montgomery arithmetic -- doesn't seem worth it
  const localp_big MONTGOMERY_N = COEFF_N;

  const doubleword MONTGOMERY_R = []{
    doubleword c;
    mpn_zero(c.data, 2*COEFF_WORDS);
    c.data[COEFF_WORDS] = 1;
    return c;
  }();

  const doubleword MONGOMERY_RR = []{
    doubleword q, r, rr;

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

  const localp_big MONTGOMERY_RINV = []{
  }();

  const localp_big MONTGOMERY_NPRIME = []{
  }();
#endif

  inline friend void __reduce(localp_big &result, doubleword a, unsigned len)
  {
    doubleword q;
    mpn_tdiv_qr(q.data, result.data, 0, a.data, len, COEFF_N.data, COEFF_WORDS);
  }

  static constexpr inline mp_limb_t powint(mp_limb_t x, mp_limb_t p) {
    return p ? (p & 1 ? x : 1)*powint(x*x, p>>1) : 1;
  }

  static constexpr mp_limb_t P_POWERS2[6] = { P,
					      powint(P,2),
					      powint(P,4),
					      powint(P,8),
					      powint(P,16),
					      powint(P,32) };
  static const mp_limb_t P_POWMAX = powint(P,MAXK(P));
  static const unsigned logMAXK = lgint64(MAXK(P));

  // return valuation v of a; set a /= P^v, p = P^v
  static unsigned val_pow(mp_limb_t &p, mp_limb_t &a) {
    unsigned v = 0;
    p = 1;
    for (int i = logMAXK; i >= 0; i--) {
      if (a % P_POWERS2[i] == 0) {
	a /= P_POWERS2[i];
	p *= P_POWERS2[i];
	v += 1 << i;
      }
    }
    return v;
  }

public:
  static const char *COEFF_ID() {
    static char s[100];
    sprintf(s, "ℤ/%" PRIu64 "^%u as mp_limb_t[%u]", P, K, COEFF_WORDS);
    return s;
  }

  inline size_t hash() const {
    size_t seed = COEFF_WORDS;
    for (unsigned i = 0; i < COEFF_WORDS; i++)
      seed ^= data[i] + 0x9e3779b9 + (seed << 6) + (seed >> 2);
    return seed;
  }

  inline bool nz_p() const { return !mpn_zero_p(data, COEFF_WORDS); }

  inline bool z_p() const { return !nz_p(); }

  /* returns true if a in [0,b) or b=0 */
  inline bool reduced_p(const localp_big &b) const {
    return b.z_p() || cmp(b) < 0;
  }

  inline void set(const localp_big &a) { mpn_copyi(data, a.data, COEFF_WORDS); }

  inline void set_si(const int64_t a) {
    if (a >= 0) {
      zero();
      data[0] = a;
    } else
      mpn_sub_1(data, COEFF_N.data, COEFF_WORDS, -a);
  }

  inline int64_t get_si() const {
    int sign = 0;
    for (int i = COEFF_WORDS-1; i >= 0; i--) {
      if (data[i] == COEFF_N.data[i])
	continue;
      if (data[i] == 0 && sign >= 0)
	sign = 1;
      else if (data[i] == COEFF_N.data[i]-1 && sign <= 0)
	sign = -1;
      else
	throw std::runtime_error("get_si() does not fit in an int64_t");
    }

    if (sign >= 0)
      return data[0];
    else
      return data[0] - COEFF_N.data[0];
  }

  inline void zero() { mpn_zero(data, COEFF_WORDS); }

  inline void add(const localp_big &a, const localp_big &b) {
    mp_limb_t carry = mpn_add_n(data, a.data, b.data, COEFF_WORDS);

    if (carry || mpn_cmp(data, COEFF_N.data, COEFF_WORDS) >= 0)
      mpn_sub_n(data, data, COEFF_N.data, COEFF_WORDS);
  }

  inline void add_si(const localp_big &a, int64_t b) {
    if (b >= 0) {
      mp_limb_t carry = mpn_add_1(data, a.data, COEFF_WORDS, b);
      if (carry || mpn_cmp(data, COEFF_N.data, COEFF_WORDS) >= 0)
	mpn_sub_n(data, data, COEFF_N.data, COEFF_WORDS);
    } else {
      mp_limb_t carry = mpn_sub_1(data, a.data, COEFF_WORDS, -b);
      if (carry)
	mpn_add_n(data, data, COEFF_N.data, COEFF_WORDS);
    }
  }

  inline void addmul(const localp_big &a, const localp_big &b) {
    localp_big c;
    c.mul(a, b);
    add(*this, c);
  }

  inline int cmp(const localp_big &b) const {
    return mpn_cmp(data, b.data, COEFF_WORDS);
  }

  inline int cmp_si(int64_t b) const {
    if (b >= 0)
      return data[0] != (uint64_t) b || !mpn_zero_p(data+1, COEFF_WORDS-1);
    else {
      localp_big c;
      mpn_add_1(c.data, data, COEFF_WORDS, -b);
      return c.cmp(COEFF_N);
    }
  }

  inline friend void fdiv_qr(localp_big &q, localp_big &r, const localp_big &a, const localp_big &b) {
    localp_big __a = a, __b = b, __c = __mpn_ui(1);

    // set __c = P^v, __b = b/P^v with v maximal
    mp_limb_t __r, p;
    while ((__r = mpn_divrem_1(__b.data, 0, __b.data, COEFF_WORDS, P_POWMAX)) == 0)
      mpn_mul_1(__c.data, __c.data, COEFF_WORDS, P_POWMAX);

    val_pow(p, __r);    
    mpn_mul_1(__b.data, __b.data, COEFF_WORDS, P_POWMAX/p);
    mpn_add_1(__b.data, __b.data, COEFF_WORDS, __r);
    mpn_mul_1(__c.data, __c.data, COEFF_WORDS, p);
    
    // divide by __c with remainder
    unsigned nzlimbs = __nzlimbs(__c.data, COEFF_WORDS);
    q.zero();
    r.zero();
    mpn_tdiv_qr(q.data, r.data, 0, __a.data, COEFF_WORDS, __c.data, nzlimbs);

    // divide  quotient by __b
    __b.inv(__b);
    q.mul(q, __b);
  }

  inline friend uint64_t fdiv_qr_ui(localp_big &q, localp_big &r, const localp_big &a, uint64_t b) {
    uint64_t __c = 1;
    for (int i = logMAXK; i >= 0; i--) {
      if (b % P_POWERS2[i] == 0) {
	b /= P_POWERS2[i];
	__c *= P_POWERS2[i];
      }
    }
    localp_big binv = __mpn_ui(b);
    binv.inv(binv);
    uint64_t __r = mpn_divrem_1(q.data, 0, a.data, COEFF_WORDS, __c);
    q.mul(q, binv);
    r = __mpn_ui(__r);
    return __r;
  }
  
  inline friend void shdiv_qr(localp_big &q, localp_big &r, const localp_big &a, const localp_big &b) {
    unsigned nzlimbs = __nzlimbs(b.data, COEFF_WORDS);
    localp_big __q, __r;
    __q.zero();
    __r.zero();
    mpn_tdiv_qr(__q.data, __r.data, 0, a.data, COEFF_WORDS, b.data, nzlimbs);
    q.set(__q);
    r.set(__r);
  }

  inline friend uint64_t shdiv_qr_ui(localp_big &q, localp_big &r, const localp_big &a, uint64_t b) {
    uint64_t __r = mpn_divrem_1(q.data, 0, a.data, COEFF_WORDS, b);
    r = __mpn_ui(__r);
    return __r;
  }
  
  /* modular inverse. result*a == 1 mod COEFF_N */
  inline void inv(const localp_big &a) {
    localp_big g;
    doubleword s;
    mp_size_t slen;
    {
      localp_big a0 = a, m0 = COEFF_N;
      if (mpn_gcdext(g.data, s.data, &slen, a0.data, COEFF_WORDS, m0.data, COEFF_WORDS) != 1 || g.data[0] != 1)
	throw std::runtime_error("inv() of non-invertible element");
    }
    if (slen < 0)
      mpn_sub(data, COEFF_N.data, COEFF_WORDS, s.data, -slen);
    else {
      mpn_copyi(data, s.data, slen);
      mpn_zero(data+slen, COEFF_WORDS-slen);
    }
  }

  inline void mul(const localp_big &a, const localp_big &b) {
    doubleword temp;
    mpn_mul_n(temp.data, a.data, b.data, COEFF_WORDS);
    __reduce(*this, temp, 2*COEFF_WORDS);
  }

  inline void mul_si(const localp_big &a, int64_t b) {
    doubleword temp;
    if (b >= 0)
      temp.data[COEFF_WORDS] = mpn_mul_1(temp.data, a.data, COEFF_WORDS, b);
    else
      temp.data[COEFF_WORDS] = mpn_mul_1(temp.data, a.data, COEFF_WORDS, -b);
    __reduce(*this, temp, COEFF_WORDS+1);
    if (b < 0 && !z_p())
      mpn_sub_n(data, COEFF_N.data, data, COEFF_WORDS);
  }

  inline void neg(const localp_big &a) {
    if (z_p())
      zero();
    else
      mpn_sub_n(data, COEFF_N.data, a.data, COEFF_WORDS);
  }

  inline int sgn() const {
    return nz_p();
  }

  inline void sub(const localp_big &a, const localp_big &b) {
    mp_limb_t carry = mpn_sub_n(data, a.data, b.data, COEFF_WORDS);
    if (carry)
      mpn_add_n(data, data, COEFF_N.data, COEFF_WORDS);
  }

  inline void submul(const localp_big &a, const localp_big &b) {
    localp_big c;
    c.mul(a, b);
    sub(*this, c);
  }

  /* P-valuation of a.
     Set result to a / largest power of P dividing it */
  inline unsigned val(const localp_big &a) {
    if (a.z_p()) {
      zero();
      return UINT_MAX;
    }
    
    set(a);
    unsigned v = 0;
    mp_limb_t r, p;

    while ((r = mpn_divrem_1(data, 0, data, COEFF_WORDS, P_POWMAX)) == 0)
      v += MAXK(P);

    v += val_pow(p, r);
    mpn_mul_1(data, data, COEFF_WORDS, P_POWMAX/p);
    mpn_add_1(data, data, COEFF_WORDS, r);
    return v;
  }
  
  /* gcd = s*a + t*b */
  inline friend void gcdext(localp_big &gcd, localp_big &s, localp_big &t, const localp_big &a, const localp_big &b) {
#if 0 // 0 has valuation K, everything fine
    if (z_p(a)) {
      set(gcd, b);
      set_si(s, 0);
      set_si(t, 1);
      return;
    }
    if (z_p(b)) {
      set(gcd, a);
      set_si(s, 1);
      set_si(t, 0);
      return;
    }
#endif

    localp_big va, vb;
    unsigned vala = va.val(a), valb = vb.val(b);

    if (vala > valb) {
      gcd = __mpn_pow_ui(__mpn_ui(P), valb);
      s.zero();
      t.inv(vb);
    } else {
      gcd = __mpn_pow_ui(__mpn_ui(P), vala);
      s.inv(va);
      t.zero();
    }
  }

  /* returns unit and generator of annihilator ideal:
     a*unit is canonical (P^n) and a*annihilator=0 */
  inline friend void unit_annihilator(localp_big &unit, localp_big &annihilator, const localp_big &a) {
    if (a.z_p()) {
      unit.zero();
      annihilator.set_si(1);
      return;
    }

    localp_big va;
    unsigned vala = va.val(a);
    unit.inv(va);
    annihilator = __mpn_pow_ui(__mpn_ui(P), K-vala);
  }

  inline char *get_str(char *s, int base) const {
    char *p;

    mp_limb_t temp[COEFF_WORDS];
    mpn_copyi(temp, data, COEFF_WORDS);
    unsigned nzlimbs = __nzlimbs(temp, COEFF_WORDS);
    size_t digits = mpn_sizeinbase(temp, nzlimbs, 10);

    if (s == NULL)
      p = (char *) malloc(digits+1);
    else
      p = s;

    digits = mpn_get_str((unsigned char *) p, base, temp, nzlimbs);
    for (unsigned i = 0; i < digits; i++)
      p[i] += '0';
    p[digits] = 0;

    if (s == NULL)
      p = (char *) realloc(p, digits+1);

    return p;
  }

  inline int out_str(FILE *f) const {
    char *s = (char *) get_str(nullptr, 10, *this);
    fprintf(f, "%s", s); /* maybe we should print in base P? */
    int digits = strlen(s);
    free(s);
  
    return digits;
  }

  /* conversions */
};

template<uint64_t P, unsigned K> const localp_big<P,K> localp_big<P,K>::COEFF_N = __mpn_pow_ui(__mpn_ui(P), K);

template<uint64_t P, unsigned K> constexpr mp_limb_t localp_big<P,K>::P_POWERS2[];
