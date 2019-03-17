template<unsigned K> class __ring0 {
  mp_limb_t data[K];

  inline static unsigned __nzlimbs(const mp_limb_t *a, unsigned na) {
    while (na > 0 && a[na-1] == 0) na--;
    return na;
  }
  
  // integers are thought of as K limbs and an infinite "period", 0 or -1
  mp_limb_t period() const { return 0 > (int64_t) data[K-1] ? -1ULL : 0; }
public:
  static const char *COEFF_ID() {
    static char s[100];
    sprintf(s, "ℤ as mp_limb_t[%u]", K);
    return s;
  }

  inline void init() { }

  inline void init_set(const __ring0 &a) { set(a); }

  inline void init_set_si(int64_t a) { set_si(a); }

  inline void clear() { }

  size_t hash() {
    size_t seed = K;
    for (unsigned i = 0; i < K; i++)
      seed ^= data[i] + 0x9e3779b9 + (seed << 6) + (seed >> 2);
    return seed;
  }

  inline bool nz_p() const { return !mpn_zero_p(data,K); }

  inline bool z_p() const { return mpn_zero_p(data,K); }

  inline bool reduced_p(const __ring0 &b) const {
    return b.z_p() || (sgn() >= 0 && cmp(b) < 0);
  }

  inline void set(const __ring0 &a) { mpn_copyi(data, a.data, K); }

  inline void set_si(int64_t a) {
    data[0] = a;
    if (a >= 0)
      mpn_zero(data+1, K-1);
    else
      for (unsigned i = 1; i < K; i++) data[i] = -1ULL;
  }

  inline int64_t get_si() const {
    int64_t r = data[0];
    mp_limb_t sign = r >= 0 ? 0 : -1ULL;
    for (unsigned i = 1; i < K; i++)
      if (data[i] != sign)
	throw std::runtime_error("get_si() doesn't fit in an int64_t");
    return r;
  }

  void zero() { mpn_zero(data, K); }

  inline void add(const __ring0 &a, const __ring0 &b) {
    mp_limb_t carry = a.period() ^ b.period();
    carry ^= -mpn_add_n(data, a.data, b.data, K);
    /*
+ +: +, carry=0
+ -: +, carry=1
+ -: -, carry=0
- -: -, carry=1
    */
    if (carry != period())
      throw std::runtime_error("add() integer overflow");
  }

  inline void add_si(const __ring0 &a, int64_t b) {
    /*
+ +: +, carry=0
+ -: +, borrow=0
+ -: -, borrow=1
- +: +, carry=1
- +: -, borrow=0
- -: -, borrow=0
    */
    mp_limb_t carry = a.period();
    carry ^= (b >= 0) ? -mpn_add_1(data, a.data, K, b) : -mpn_sub_1(data, a.data, K, -b);
    if (carry != period())
      throw std::runtime_error("add_si() integer overflow");
  }

  inline void addmul(const __ring0 &a, const __ring0 &b) {
    __ring0 m;
    m.mul(a, b);
    add(*this, m);
  }

  inline int cmp(const __ring0 &b) const {
    if (period()) {
      if (b.period())
	return mpn_cmp(b.data, data, K);
      else
	return -1;
    } else {
      if (b.period())
	return 1;
      else
	return mpn_cmp(data, b.data, K);
    }
  }

  inline int cmp_si(int64_t b) const {
    if (b >= 0) {
      if (period()) return -1;
      for (unsigned i = 1; i < K; i++) if (data[i] != 0) return 1;
      return (data[0] > b) - (data[0] < b);
    } else {
      if (!period()) return 1;
      for (unsigned i = 1; i < K; i++) if (data[i] != -1ULL) return -1;
      return (data[0] > (uint64_t) b) - (data[0] < (uint64_t) b);
    }
  }

  inline void divexact(const __ring0 &a, const __ring0 &b) {
    fdiv_q(a, b);
  }

  inline void fdiv_q(const __ring0 &a, const __ring0 &b) {
    __ring0 r;
    fdiv_qr(*this, r, a, b);
  }

  inline void fdiv_r(const __ring0 &a, const __ring0 &b) {
    __ring0 q;
    fdiv_qr(q, *this, a, b);
  }

  inline friend void fdiv_qr(__ring0 &q, __ring0 &r, const __ring0 &a, const __ring0 &b) {
    bool asign = a.period(), bsign = b.period();
    __ring0 __a, __b;
    if (asign) __a.neg(a); else __a.set(a);
    if (bsign) __b.neg(b); else __b.set(b);
    unsigned nzlimbs = __nzlimbs(__b.data, K);
    q.zero(); r.zero();
    mpn_tdiv_qr(q.data, r.data, 0, __a.data, K, __b.data, nzlimbs);
    if (asign != bsign) {
      q.neg(q);
      if (!mpn_zero_p(r.data, K)) {
	r.sub(__b, r);
	q.add_si(q, -1);
      }
    }
  }

  inline friend uint64_t fdiv_ui(const __ring0 &a, uint64_t b) {
    __ring0 q, r;
    return fdiv_qr_ui(q, r, a, b);
  }

  inline uint64_t fdiv_q_ui(const __ring0 &a, uint64_t b) {
    __ring0 r;
    return fdiv_qr_ui(*this, r, a, b);
  }

  inline uint64_t fdiv_r_ui(const __ring0 &a, uint64_t b) {
    __ring0 q;
    return fdiv_qr_ui(q, *this, a, b);
  }
    
  inline friend uint64_t fdiv_qr_ui(__ring0 &q, __ring0 &r, const __ring0 &a, uint64_t b) {
    bool asign = a.period();
    __ring0 __a;
    if (asign) __a.neg(a); else __a.set(a);
    q.zero(); r.zero();
    r.data[0] = mpn_divrem_1(q.data, 0, __a.data, K, b);
    if (asign) {
      q.neg(q);
      if (r.data[0] != 0) {
	r.data[0] = b - r.data[0];
	q.add_si(q, -1);
      }
    }
    return r.data[0];
  }

  inline void mul(const __ring0 &a, const __ring0 &b) {
    mp_limb_t temp[2*K];
    mpn_mul(temp, a.data, K, b.data, K);
    if (a.period())
      mpn_sub_n(temp+K, temp+K, b.data, K);
    if (b.period())
      mpn_sub_n(temp+K, temp+K, a.data, K);
    mpn_copyi(data, temp, K);
    for (unsigned i = K; i < 2*K; i++)
      if (temp[i] != period())
	throw std::runtime_error("mul() integer overflow");
  }

  inline void mul_si(const __ring0 &a, int64_t b) {
    mp_limb_t carry = mpn_mul_1 (data, a.data, K, (b >= 0) ? b : -b);
    if (carry != period())
      throw std::runtime_error("mul() integer overflow");
    if (b < 0)
      neg(*this);
  }

  inline void neg(const __ring0 &a) {
    mp_limb_t carry = a.period();
    carry ^= -mpn_neg(data, a.data, K);
    if (carry != period())
      throw std::runtime_error("neg() integer overflow");
  }
    
  inline int sgn() const {
    if (mpn_zero_p(data, K))
      return 0;
    else if (period())
      return -1;
    else return 1;
  }

  inline void sub(const __ring0 &a, const __ring0 &b) {
    /*
+ +: +, borrow=0
+ +: -, borrow=1
+ -: +, borrow=1
- +: -, borrow=0
- -: +, borrow=0
- -: -, borrow=1
    */
    mp_limb_t carry = a.period() ^ b.period();
    carry ^= -mpn_sub_n(data, a.data, b.data, K);
    if (carry != period())
      throw std::runtime_error("sub() integer overflow");
  }

  inline void submul(const __ring0 &a, const __ring0 &b) {
    __ring0 m;
    m.mul(a, b);
    sub(*this, m);
  }

  friend void gcdext(__ring0 &gcd, __ring0 &s, __ring0 &t, const __ring0 &a, const __ring0 &b) {
    __ring0 new_s, new_t, new_gcd;
    bool asign = a.period(), bsign = b.period();
    if (bsign) new_gcd.neg(b); else new_gcd.set(b);
    if (asign) gcd.neg(a); else gcd.set(a);
    new_s.set_si(0); s.set_si(1);
    new_t.set_si(1); t.set_si(0);

    while (new_gcd.nz_p()) {
      __ring0 q;
      q.fdiv_q(gcd, new_gcd);
      s.submul(q, new_s); s.swap(new_s);
      t.submul(q, new_t); t.swap(new_t);
      gcd.submul(q, new_gcd); gcd.swap(new_gcd);
    }
    if (asign) s.neg(s);
    if (bsign) t.neg(t);
  }

  inline int out_str(FILE *f) const {
    char *s = (char *) get_str(nullptr, 10, *this);
    fprintf(f, "%s", s);
    int digits = strlen(s);
    free(s);
    return digits;
  }

  inline char *get_str(char *s, int base) const {
    char *p;
    bool sign = period() != 0;
    
    mp_limb_t temp[K];
    if (sign)
      mpn_neg(temp, data, K);
    else
      mpn_copyi(temp, data, K);
    unsigned nzlimbs = __nzlimbs(temp, K);
    size_t digits = mpn_sizeinbase(temp, nzlimbs, 10);

    if (s == NULL)
      p = (char *) malloc(digits+1+sign);
    else
      p = s;

    if (sign)
      *p = '-';
    
    digits = mpn_get_str((unsigned char *) p+sign, base, temp, nzlimbs);
    for (unsigned i = 0; i < digits; i++)
      p[i+sign] += '0';
    p[digits+sign] = 0;

    if (s == NULL)
      p = (char *) realloc(p, digits+1+sign);

    return p;
  }

  void swap(__ring0 &b) {
    __ring0 tmp;
    tmp.set(*this);
    set(b);
    b.set(tmp);
  }
};
