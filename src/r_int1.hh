/* COEFF_UNSAFE turns off coefficient overflow detection. It's
   generally a bad idea to disable it, but it's only present in GCC >=
   5 */
#if defined(__GNUC__) && __GNUC__ >= 5
#define COEFF_SAFE
#elif defined(__clang__) && __has_builtin(__builtin_saddll_overflow)
#define COEFF_SAFE
#endif
#ifndef COEFF_SAFE
#define COEFF_UNSAFE
#endif

template<> class __ring0<1> {
  int64_t data;
public:
  static const char *COEFF_ID() {
    return "ℤ as int64_t";
  }

  inline void init() { }

  inline void init_set(const __ring0 &a) { set(a); }

  inline void init_set_si(int64_t a) { this->set_si(a); }

  inline void clear() { }

  inline size_t hashkey() const { return data; }

  inline bool nz_p() const { return data != 0; }

  inline bool z_p() const { return data == 0; }

  inline bool reduced_p(const __ring0 &b) const {
    return b.data == 0 || (data >= 0 && data < b.data);
  }

  inline void set(const __ring0 &a) { data = a.data; }

  inline void set_si(int64_t a) { data = a; }

  inline int64_t get_si() const {
    return data;
  }

  void zero() { data = 0; }
  
  inline void add(const __ring0 &a, const __ring0 &b) {
    add_si(a, b.data);
  }

  inline void add_si(const __ring0 &a, int64_t b) {  
#ifdef COEFF_UNSAFE
    data = a.data + b;
#else
    if (__builtin_expect(__builtin_saddll_overflow(a.data, b, (long long *) &data), false))
      throw std::runtime_error("add(): coefficient overflow");
#endif
  }

  inline void addmul(const __ring0 &a, const __ring0 &b) {
    __ring0 m;
    m.mul(a, b);
    add(*this, m);
  }

  inline int cmp(const __ring0 &b) const {
    return cmp_si(b.data);
  }

  inline int cmp_si(int64_t b) const {
    return (data > b) - (data < b);
  }

  inline void divexact(const __ring0 &a, const __ring0 &b) {
    data = a.data / b.data;
  }
  
  inline void fdiv_q(const __ring0 &a, const __ring0 &b) {
    int64_t r = a.data % b.data;
    data = a.data / b.data;
    if (r < 0) data--; /* C rounds quotient to 0, not down */
  }

  inline void fdiv_r(const __ring0 &a, const __ring0 &b) {
    int64_t r = a.data % b.data;
    data = (r < 0) ? r + b.data : r;
  }

  inline friend void fdiv_qr(__ring0 &q, __ring0 &r, const __ring0 &a, const __ring0 &b) {
    int64_t __r = a.data % b.data, __q = a.data / b.data;
    if (__r < 0)
      r.data = __r+b.data, q.data = __q-1;
    else
      r.data = __r, q.data = __q;
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
    int64_t __b = (int64_t) b;
    if (__b >= 0) {
      int64_t __r = a.data % __b, __q = a.data / __b;
      if (__r < 0)
	r.data = __r+b, q.data = __q-1;
      else
	r.data = __r, q.data = __q;
    } else
      q.data = 0, r.data = b;

    return (uint64_t) r.data;
  }

  inline void mul(const __ring0 &a, const __ring0 &b) {
    mul_si(a, b.data);
  }
  
  inline void mul_si(const __ring0 &a, int64_t b) {
#ifdef COEFF_UNSAFE
    data = a.data * b;
#else
    if (__builtin_expect(__builtin_smulll_overflow(a.data, b, (long long *) &data), false))
      throw std::runtime_error("mul(): coefficient overflow");
#endif
  }

  inline void neg(const __ring0 &a) {
#ifdef COEFF_UNSAFE
    data = -a.data;
#else
    if (__builtin_expect(__builtin_ssubll_overflow(0, a.data, (long long *) &data), false))
      throw std::runtime_error("neg(): coefficient overflow");
#endif
  }

  inline int sgn() const {
    return cmp_si(0);
  }
  
  inline void sub(const __ring0 &a, const __ring0 &b) {
#ifdef COEFF_UNSAFE
    data = a.data - b.data;
#else
    if (__builtin_expect(__builtin_ssubll_overflow(a.data, b.data, (long long *) &data), false))
      throw std::runtime_error("sub(): coefficient overflow");
#endif
  }

  inline void submul(const __ring0 &a, const __ring0 &b) {
    __ring0 m;
    m.mul(a, b);
    sub(*this, m);
  }

  /* Set g to the greatest common divisor of a and b, and in addition
     set s and t to coefficients satisfying a*s + b*t = g. The value
     in g is always positive, even if one or both of a and b are
     negative (or zero if both inputs are zero). The values in s and t
     are chosen such that normally, abs(s) < abs(b) / (2 g) and abs(t)
     < abs(a) / (2 g), and these relations define s and t
     uniquely. There are a few exceptional cases:

     If abs(a) = abs(b), then s = 0, t = sgn(b).

     Otherwise, s = sgn(a) if b = 0 or abs(b) = 2 g, and t = sgn(b) if
     a = 0 or abs(a) = 2 g.

     In all cases, s = 0 if and only if g = abs(b), i.e., if b divides
     a or a = b = 0.
  */
  friend void gcdext(__ring0 &gcd, __ring0 &s, __ring0 &t, const __ring0 &a, const __ring0 &b) {
    __ring0 new_s, new_t, new_gcd;
    bool asign = a.data<0, bsign = b.data<0;
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
    return fprintf(f, "%" PRId64, data);
  }

  char *get_str(char *s, int base) const {
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
    trio_sprintf(p, "%..*" PRId64, base, data);
#ifdef __clang__
#pragma clang diagnostic pop
#elif defined(__GNUC__)
#pragma GCC diagnostic pop
#endif
#else
    sprintf(p, "%" PRId64, data);
#endif
    if (s == nullptr)
      p = (char *) realloc(p, strlen(p)+1);

    return p;
  }

  void swap(__ring0 &b) {
    __ring0 tmp;
    tmp.set(*this);
    set(b);
    b.set(tmp);
  }
  
  // conversions
  template<unsigned L> friend class __ring0;
  template<uint64_t Q, unsigned L> friend class __localp_small;
  template<uint64_t Q, unsigned L> friend class __localp_big;
  template<unsigned L> friend class __local2_small;
  template<unsigned L> friend class __local2_big;

  template<unsigned L> inline void map(const __ring0<L> &a) {
    set_si(a.get_si());
  }

  inline void map(const __ring0_mpz &a) {
    set_si(a.get_si());
  }

  inline void map(const __ring0_64 &a) {
    set(a);
  }
  
  template<unsigned L> inline void map(const __local2_big<L> &a) {
    data = a.data[0];
    for (unsigned i = 1; i < a.COEFF_WORDS; i++)
      if (a.data[i] != 0 || data < 0)
	throw std::runtime_error("map(): data cannot fit in an int64_t");
  }

  template<unsigned L> inline void map(const __local2_small<L> &a) {
    data = a.data;
    if (data < 0)
      throw std::runtime_error("map(): cannot fit in an int64_t");
  }

  template<uint64_t P, unsigned L> inline void map(const __localp_big<P,L> &a) {
    set_si(a.get_si());
  }

  template<uint64_t P, unsigned L> inline void map(const __localp_small<P,L> &a) {
    set_si(a.get_si());
  }
};

// moved from r_int0.hh, because then template was not yet specialized
inline void __ring0<0>::map(const __ring0_64 &a) {
  mpz_set_si(data, a.data);
}
