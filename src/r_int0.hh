template<> class __ring0<0> {
  mpz_t data;
public:
  static const char *COEFF_ID() { return "ℤ as mpz_t"; }

  inline void init() { mpz_init(data); }

  inline void init_set(const __ring0 &a) { mpz_init_set(data, a.data); }

  inline void init_set_si(int64_t a) { mpz_init_set_si(data, a); }

  inline void clear() { mpz_clear(data); }

  size_t hash() const {
    size_t seed = data->_mp_size;
    for (unsigned i = 0; i < abs(data->_mp_size); i++)
      seed ^= data->_mp_d[i] + 0x9e3779b9 + (seed << 6) + (seed >> 2);
    return seed;
  }

  inline bool nz_p() const { return mpz_sgn(data) != 0; }

  inline bool z_p() const { return mpz_sgn(data) == 0; }

  inline bool reduced_p(const __ring0 &b) const {
    return !mpz_sgn(b.data) || (mpz_sgn(data) >= 0 && mpz_cmp(data, b.data) < 0);
  }

  inline void set(const __ring0 &a) { mpz_set(data, a.data); }

  inline void set_si(int64_t a) { mpz_set_si(data, a); }

  inline int64_t get_si() const { return mpz_get_si(data); }

  void zero() { mpz_set_si(data, 0); }
  
  inline void add(const __ring0 &a, const __ring0 &b) {
    mpz_add(data, a.data, b.data);
  }

  inline void add_si(const __ring0 &a, int64_t b) {  
    if (b >= 0)
      mpz_add_ui(data, a.data, b);
    else
      mpz_sub_ui(data, a.data, -b);
  }

  inline void addmul(const __ring0 &a, const __ring0 &b) {
    mpz_addmul(data, a.data, b.data);
  }

  inline int cmp(const __ring0 &b) const {
    return mpz_cmp(data, b.data);
  }

  inline int cmp_si(int64_t b) const {
    return mpz_cmp_si(data, b);
  }

  inline void divexact(const __ring0 &a, const __ring0 &b) {
    mpz_divexact(data, a.data, b.data);
  }
  
  inline void fdiv_q(const __ring0 &a, const __ring0 &b) {
    mpz_fdiv_q(data, a.data, b.data);
  }

  inline void fdiv_r(const __ring0 &a, const __ring0 &b) {
    mpz_fdiv_r(data, a.data, b.data);
  }

  inline friend void fdiv_qr(__ring0 &q, __ring0 &r, const __ring0 &a, const __ring0 &b) {
    mpz_fdiv_qr(q.data, r.data, a.data, b.data);
  }

  inline friend uint64_t fdiv_ui(const __ring0 &a, uint64_t b) {
    return mpz_fdiv_ui(a.data, b);
  }

  inline uint64_t fdiv_q_ui(const __ring0 &a, uint64_t b) {
    return mpz_fdiv_q_ui(data, a.data, b);
  }

  inline uint64_t fdiv_r_ui(const __ring0 &a, uint64_t b) {
    return mpz_fdiv_r_ui(data, a.data, b);
  }
    
  inline friend uint64_t fdiv_qr_ui(__ring0 &q, __ring0 &r, const __ring0 &a, uint64_t b) {
    return mpz_fdiv_qr_ui(q.data, r.data, a.data, b);
  }

  inline void mul(const __ring0 &a, const __ring0 &b) {
    mpz_mul(data, a.data, b.data);
  }
  
  inline void mul_si(const __ring0 &a, int64_t b) {
    mpz_mul_si(data, a.data, b);
  }

  inline void neg(const __ring0 &a) {
    mpz_neg(data, a.data);
  }

  inline int sgn() const {
    return mpz_sgn(data);
  }

  inline void sub(const __ring0 &a, const __ring0 &b) {
    mpz_sub(data, a.data, b.data);
  }

  inline void submul(const __ring0 &a, const __ring0 &b) {
    mpz_submul(data, a.data, b.data);
  }

  inline friend void gcdext(__ring0 &gcd, __ring0 &s, __ring0 &t, const __ring0 &a, const __ring0 &b) {
    mpz_gcdext(gcd.data, s.data, t.data, a.data, b.data);
  }

  inline int out_str(FILE *f) const {
    return mpz_out_str(f, 10, data);
  }

  inline char *get_str(char *s, int base) const {
    return mpz_get_str(s, base, data);
  }

  void swap(__ring0 &b) {
    mpz_swap(data, b.data);
  }

  // conversions
  template<unsigned L> friend class __ring0;
  template<uint64_t Q, unsigned L> friend class __localp_small;
  template<uint64_t Q, unsigned L> friend class __localp_big;
  template<unsigned L> friend class __local2_small;
  template<unsigned L> friend class __local2_big;

  template<unsigned L> inline void map(const __ring0<L> &a) {
    if (a.period()) {
      __ring0<L> b;
      b.neg(a);
      map(b);
      neg(*this);
    } else {
      unsigned nzlimbs = __ring0<L>::__nzlimbs(a.data, L);
      mpz_realloc2(data, GMP_NUMB_BITS*nzlimbs);
      mpn_copyi(data[0]._mp_d, a.data, nzlimbs);
      data[0]._mp_size = nzlimbs;
    }
  }

  inline void map(const __ring0_mpz &a) {
    mpz_set(data, a.data);
  }

  inline void map(const __ring0_64 &a); // will come later, when __ring0_64 is specialized
  
  template<unsigned L> inline void map(const __local2_big<L> &a) {
    unsigned nzlimbs = __local2_big<L>::__nzlimbs(a.data, a.COEFF_WORDS);
    mpz_realloc2(data, GMP_NUMB_BITS*nzlimbs);
    mpn_copyi(data[0]._mp_d, a.data, nzlimbs);
    data[0]._mp_size = nzlimbs;
  }

  template<unsigned L> inline void map(const __local2_small<L> &a) {
    mpz_set_ui(data, a.data);
  }

  template<uint64_t P, unsigned L> inline void map(const __localp_big<P,L> &a) {
    unsigned nzlimbs = __localp_big<P,L>::__nzlimbs(a.data, a.COEFF_WORDS);
    mpz_realloc2(data, GMP_NUMB_BITS*nzlimbs);
    mpn_copyi(data[0]._mp_d, a.data, nzlimbs);
    data[0]._mp_size = nzlimbs;
  }

  template<uint64_t P, unsigned L> inline void map(const __localp_small<P,L> &a) {
    mpz_set_ui(data, __localp_small<P,L>::c2uint64_t(a));
  }
};
