template<uint64_t P, unsigned K> class __localp_small {
  static constexpr uint64_t powint64(uint64_t x, uint64_t p) {
    return p ? ((p & 1) ? x : 1)*powint64(x*x, p>>1) : 1;
  }

  static constexpr unsigned lgint64(uint64_t n) {
    return n ? 1+lgint64(n/2) : -1;
  }

  static constexpr uint64_t gcd64(uint64_t a, uint64_t b) {
    return a ? gcd64(b%a, a) : b;
  }

  typedef unsigned __int128 uint128_t; // for intermediate results
  typedef signed __int128 int128_t; // for intermediate results

  static inline int print_u128_t(uint128_t u128) {
    const uint64_t P10_UINT64 = 10000000000000000000ULL; /* 19 zeroes */
    int rc;
    if (u128 > UINT64_MAX) {
      uint128_t leading  = u128 / P10_UINT64;
      uint64_t  trailing = u128 % P10_UINT64;
      rc = print_u128_t(leading);
      rc += printf("%.19" PRIu64, trailing);
    } else {
      uint64_t u64 = u128;
      rc = printf("%" PRIu64, u64);
    }
    return rc;
  }
  
  /* returns the s such that s*a + t*b = (a,b).
     invoke with gcdext(a, b, 1, 0, 0, 1).
     recursion invariant is s*a0 + t*b0 = a, u*a0 + v*b0 = b.
  */
  static constexpr int128_t gcdext128(uint128_t a, uint128_t b, int128_t s, int128_t t, int128_t u, int128_t v) {
    return a ? gcdext128(b%a, a, u-(b/a)*s, v-(b/a)*t, s, t) : u;
  }

  static const uint64_t MONTGOMERY_N = powint64(P, K);

  static const uint128_t MONTGOMERY_R = ((uint128_t) 1) << 64;

  static const uint64_t MONTGOMERY_RR = ((MONTGOMERY_R % MONTGOMERY_N) * (MONTGOMERY_R % MONTGOMERY_N)) % MONTGOMERY_N;

  static const uint64_t MONTGOMERY_RINV = (gcdext128(MONTGOMERY_R, MONTGOMERY_N, 1, 0, 0, 1) + MONTGOMERY_N) % MONTGOMERY_N;

  static const uint64_t MONTGOMERY_NPRIME = -gcdext128(MONTGOMERY_N, MONTGOMERY_R, 1, 0, 0, 1);

  static const inline uint64_t montgomery_redc(uint128_t T) {
    uint64_t t_lo = T;
    uint128_t m = t_lo * MONTGOMERY_NPRIME;
    uint128_t s = T + m * MONTGOMERY_N;
    uint128_t u = s >> 64;
    if (s < T) u += MONTGOMERY_R - MONTGOMERY_N; // lost carry
    if (u >= MONTGOMERY_N) u -= MONTGOMERY_N;
    return u;
  }

  static inline __localp_small int64_t2c(int64_t l) {
    uint64_t v = montgomery_redc((uint128_t) MONTGOMERY_RR * (l >= 0 ? l : -l));
    return { .data = (l < 0 && v != 0) ? MONTGOMERY_N - v : v };
  }

  static const inline __localp_small uint64_t2c(uint64_t l) {
    return { .data = montgomery_redc((uint128_t) MONTGOMERY_RR * l) };
  }

  static const inline uint64_t c2uint64_t(const __localp_small c) {
    return montgomery_redc(c.data);
  }

  static constexpr int64_t inverse_mod_p_rec(uint64_t a, uint64_t b, int64_t s, int64_t u) {
    return a ? inverse_mod_p_rec(b%a, a, u-(b/a)*s, s) : u;
  }

  static const inline uint64_t inverse_mod_p(uint64_t a) {
    int64_t i = inverse_mod_p_rec(a, P, 1, 0);
    if (i < 0) return i + P; else return i;
  }

  static const constexpr uint64_t P_POWERS2[6] = { P,
						   powint64(P,2),
						   powint64(P,4),
						   powint64(P,8),
						   powint64(P,16),
						   powint64(P,32) };
  static const unsigned logK = lgint64(K);
  
  static uint64_t powP(unsigned e) {
    uint64_t p = 1;
    for (int i = logK; i >= 0; i--)
      if (e & (1LL << i)) p *= P_POWERS2[i];
    return p;
  }
public:
  uint64_t data;

  static const char *COEFF_ID() {
    static char s[100];
    sprintf(s, "ℤ/%" PRIu64 "^%u as uint64_t", P, K);
    return s;
  }

  inline size_t hash() const { return data; }

  inline bool nz_p() const { return data != 0; }

  inline bool z_p() const { return data == 0; }

  /* returns true if a in [0,b) or b=0 */
  inline bool reduced_p(const __localp_small &b) const {
    return b.data == 0 || c2uint64_t(*this) < c2uint64_t(b);
  }

  inline void set(const __localp_small &a) { data = a.data; }

  inline void set_si(const int64_t a) { *this = int64_t2c(a); }

  inline void zero() { data = 0; }
  
  inline int64_t get_si() const {
    uint64_t r = montgomery_redc(data);
    if (r > MONTGOMERY_N/2)
      return r-MONTGOMERY_N;
    else
      return r;
  }

  inline void add(const __localp_small &a, const __localp_small &b) {
    uint128_t sum = (uint128_t) a.data + b.data;
    if (sum >= MONTGOMERY_N)
      data = sum - MONTGOMERY_N;
    else
      data = sum;
  }

  inline void add_si(const __localp_small &a, int64_t b) {
    add(a, int64_t2c(b));
  }

  inline void addmul(const __localp_small &a, const __localp_small &b) {
    __localp_small c;
    c.mul(a, b);
    add(*this, c);
  }

  inline int cmp(const __localp_small &b) const {
    return (data > b.data) - (data < b.data);
  }

  inline int cmp_si(int64_t b) const {
    return cmp(int64_t2c(b));
  }

  inline friend void fdiv_qr(__localp_small &q, __localp_small &r, const __localp_small &a, const __localp_small &b) {
    fdiv_qr_ui(q, r, a, c2uint64_t(b));
  }

  inline friend uint64_t fdiv_qr_ui(__localp_small &q, __localp_small &r, const __localp_small &a, uint64_t b) {
    uint64_t __a = c2uint64_t(a), __c = 1;
    for (int i = logK; i >= 0; i--) {
      if (b % P_POWERS2[i] == 0) {
	b /= P_POWERS2[i];
	__c *= P_POWERS2[i];
      }
    }
    __localp_small binv;
    binv.inv(uint64_t2c(b));
    uint64_t __r = __a % __c;
    q = uint64_t2c(__a / __c); q.mul(q, binv);
    r = uint64_t2c(__r);
    return __r;
  }

  inline friend void shdiv_qr(__localp_small &q, __localp_small &r, const __localp_small &a, const __localp_small &b) {
    shdiv_qr_ui(q, r, a, c2uint64_t(b));
  }

  inline friend uint64_t shdiv_qr_ui(__localp_small &q, __localp_small &r, const __localp_small &a, uint64_t b) {
    uint64_t __a = c2uint64_t(a), __r = __a % b;
    q = uint64_t2c(__a / b);
    r = uint64_t2c(__r);
    return __r;
  }

  /* modular inverse. result*a == 1 */
  const inline void inv(const __localp_small &a) {
    if (a.data % P == 0)
      throw std::runtime_error("inv() of non-invertible element");
    
    __localp_small ainv;

    if (P == 3) // a == a^-1 mod 3
      ainv = a;
    else if (P == 5) { // a^3 == a^-1 mod 5
      ainv.mul(a, a);
      ainv.mul(ainv, a);
    } else if (P == 7) { // a^5 == a^-1 mod 7
      ainv.mul(a, a);
      ainv.mul(ainv, ainv);
      ainv.mul(a, ainv);
    } else
      ainv = uint64_t2c(inverse_mod_p(c2uint64_t(a)));

    for (unsigned i = 1; i < K; i <<= 1) {
      __localp_small temp;
      temp.set_si(2);
      temp.submul(a, ainv);
      ainv.mul(ainv, temp);
    }

    set(ainv);
  }

  inline void mul(const __localp_small &a, const __localp_small &b) {
    data = montgomery_redc((uint128_t) a.data * b.data);
  }

  inline void mul_si(const __localp_small &a, int64_t b) {
    mul(a, int64_t2c(b));
  }

  inline void neg(const __localp_small &a) {
    if (a.data == 0)
      data = 0;
    else
      data = MONTGOMERY_N - a.data;
  }

  inline int sgn() const {
    return data != 0;
  }

  inline void sub(const __localp_small &a, const __localp_small &b) {
    __localp_small temp;
    temp.data = MONTGOMERY_N - b.data;
    add(a, temp);
  }

  inline void submul(const __localp_small &a, const __localp_small &b) {
    __localp_small c;
    c.mul(a, b);
    sub(*this, c);
  }

  /* P-valuation of a.
     Set result to a / largest power of P dividing it */
  const inline unsigned val(const __localp_small &a) {
    if (a.z_p()) {
      zero();
      return UINT_MAX;
    }
    
    unsigned val = 0;
    uint64_t __a = c2uint64_t(a);
    for (int i = logK; i >= 0; i--) {
      if (__a % P_POWERS2[i] == 0) {
	__a /= P_POWERS2[i];
	val += 1LL << i;
      }
    }
    *this = uint64_t2c(__a);
    return val;
  }

  inline friend void gcdext(__localp_small &gcd, __localp_small &s, __localp_small &t, const __localp_small &a, const __localp_small &b) {
#if 0 // 0 has valuation 2^(logK+1)-1, everything fine
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

    __localp_small va, vb;
    unsigned vala = va.val(a), valb = vb.val(b);

    if (vala > valb) {
      gcd = uint64_t2c(powP(valb));
      s = uint64_t2c(0);
      t.inv(vb);
    } else {
      gcd = uint64_t2c(powP(vala));
      s.inv(va);
      t = uint64_t2c(0);
    }
  }   

  /* returns unit and generator of annihilator ideal:
     a*unit is canonical (P^n) and a*annihilator=0 */
  inline friend void unit_annihilator(__localp_small &unit, __localp_small &annihilator, const __localp_small &a) {
    if (a.data == 0) {
      unit = uint64_t2c(0);
      annihilator = uint64_t2c(1);
      return;
    }

    __localp_small va;
    unsigned vala = va.val(a);
    unit.inv(va);
    annihilator = uint64_t2c(powP(K-vala));
  }

  inline int out_str(FILE *f) const {
    return fprintf(f, "%" PRId64, get_si());
  }

  inline char *get_str(char *s, int base) const {
    char *p;
    if (s == nullptr)
      p = (char *) malloc(25);
    else
      p = s;
#ifdef TRIO_TRIO_H
#ifdef __clang__
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wall"
#else
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wformat="
#pragma GCC diagnostic ignored "-Wformat-extra-args"
#endif
    trio_sprintf(p, "%..*" PRId64, base, get_si());
#ifdef __clang__
#pragma clang diagnostic pop
#elif defined(__GNUC__)
#pragma GCC diagnostic pop
#endif
#else
    sprintf(p, "%" PRId64, get_si());
#endif
    if (s == nullptr)
      p = (char *) realloc(p, strlen(p)+1);

    return p;
  }

  // conversions
  template<unsigned L> friend class __ring0;
  template<uint64_t Q, unsigned L> friend class __localp_small;
  template<uint64_t Q, unsigned L> friend class __localp_big;
  //template<unsigned L> friend class __local2_small;
  //template<unsigned L> friend class __local2_big;

  template<unsigned L> inline void map(const __ring0<L> &a) {
    if (a.period()) {
      __ring0<L> b;
      b.neg(a);
      map(b);
      neg(*this);
    } else
      *this = uint64_t2c(mpn_mod_1(a.data, L, MONTGOMERY_N));
  }

  inline void map(const __ring0_mpz &a) {
    mp_size_t L = a.data[0]._mp_size;
    bool sign = L < 0;
    if (sign) L = -L;
    *this = uint64_t2c(mpn_mod_1(a.data[0]._mp_d, L, MONTGOMERY_N));
    if (sign)
      neg(*this);
  }

  inline void map(const __ring0_64 &a) {
    zero();
    if (a.data >= 0)
      *this = uint64_t2c(a.data);
    else
      neg(uint64_t2c(-a.data));
  }

  template<unsigned L> inline void map(const __localp_big<P,L> &a) {
    *this = uint64_t2c(mpn_mod_1(a.data, a.COEFF_WORDS, MONTGOMERY_N));
  }

  template<unsigned L> inline void map(const __localp_small<P,L> &a) {
    *this = uint64_t2c(a.c2uint64_t(a));
  }  
};

template<uint64_t P, unsigned K> constexpr uint64_t __localp_small<P,K>::P_POWERS2[];
