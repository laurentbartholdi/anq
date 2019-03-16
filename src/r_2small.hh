template<unsigned K> class local2_small {
  static const uint64_t COEFF_MASK = K == 64 ? ~0LL : ((1ULL << K) - 1);

  static inline local2_small inverse_mod_2_k(uint64_t a, unsigned shift) {
    a >>= shift;
    uint64_t inverse = a; // already 3 correct bits
    for (unsigned i = 0; i < 5; i++)
      inverse *= 2 - a*inverse;

    return { .data = inverse & COEFF_MASK };
  }

public:
  uint64_t data; // I know, it should be private; but I want aggregate inits

  static const char *COEFF_ID() {
    static char s[100];
    sprintf(s, "ℤ/2^%u as uint64_t", K);
    return s;
  }

  inline size_t hash() const { return data; }

  inline bool nz_p() const { return data != 0; }

  inline bool z_p() const { return data == 0; }

  inline bool reduced_p(const local2_small &b) const {
    return b.data == 0 || data < b.data;
  }

  inline void set(const local2_small &a) { data = a.data; }

  inline void set_si(int64_t a) { data = a & COEFF_MASK; }

  inline int64_t get_si() const {
    if (data > (COEFF_MASK >> 1) + 1)
      return data - (COEFF_MASK + 1);
    else
      return data;
  }

  void zero() { data = 0; }
  
  inline void add(const local2_small &a, const local2_small &b) {
    data = (a.data+b.data) & COEFF_MASK;
  }

  inline void add_si(const local2_small &a, int64_t b) {
    data = (a.data+b) & COEFF_MASK;
  }

  inline void addmul(const local2_small &a, const local2_small &b) {
    data = (data + a.data * b.data) & COEFF_MASK;
  }

  inline int cmp(const local2_small &b) const {
    return (data > b.data) - (data < b.data);
  }

  /* I don't know how to implement a meaningful compare on residue classes. Let's return 0 or 1 */
  inline int cmp_si(int64_t b) const {
    return data != (uint64_t) (b & COEFF_MASK);
  }

  inline friend void fdiv_qr(local2_small &q, local2_small &r, const local2_small &a, const local2_small &b) {
    fdiv_qr_ui(q, r, a, b.data);
  }

  inline friend uint64_t fdiv_qr_ui(local2_small &q, local2_small &r, const local2_small &a, uint64_t b) {
    uint64_t __r = a.data & ((b & -b) - 1);
    unsigned bval = __builtin_ctzll(b);
    q.mul_si(inverse_mod_2_k(b, bval), a.data >> bval);
    r.data = __r;
    return __r;
  }

  inline friend void shdiv_qr(local2_small &q, local2_small &r, const local2_small &a, const local2_small &b) {
    shdiv_qr_ui(q, r, a, b.data);
  }    

  inline friend uint64_t shdiv_qr_ui(local2_small &q, local2_small &r, const local2_small &a, uint64_t b) {
    uint64_t __r = a.data & (b-1);
    q.data = a.data >> __builtin_ctzll(b);
    r.data = __r;
    return __r;
  }

  inline void inv(const local2_small &a) {
    if (a.data & 1)
      *this = inverse_mod_2_k(a.data, 0);
    else
      throw std::runtime_error("inv() of non-invertible element");
  }

  inline void mul(const local2_small &a, const local2_small &b) {
    data = (a.data * b.data) & COEFF_MASK;
  }

  inline void mul_si(const local2_small &a, int64_t b) {
    data = (a.data * b) & COEFF_MASK;
  }

  inline void neg(const local2_small &a) {
    data = (-a.data) & COEFF_MASK;
  }

  inline int sgn() const {
    return data != 0;
  }

  inline void sub(const local2_small &a, const local2_small &b) {
    data = (a.data - b.data) & COEFF_MASK;
  }

  inline void submul(const local2_small &a, const local2_small &b) {
    data = (data - a.data * b.data) & COEFF_MASK;
  }

  inline unsigned val(const local2_small &a) {
    if (a.z_p()) {
      zero();
      return UINT_MAX;
    }

    unsigned aval = __builtin_ctzll(a.data);
    data = a.data >> aval;
    return aval;
  }
  
  inline friend void gcdext(local2_small &gcd, local2_small &s, local2_small &t, const local2_small &a, const local2_small &b) {
    uint64_t alowbit = a.data & -a.data, blowbit = b.data & -b.data;
    if (a.data == 0 || alowbit >= blowbit) {
      gcd.data = blowbit;
      s.data = 0;
      t = inverse_mod_2_k(b.data, __builtin_ctzll(blowbit)); // b.data / blowbit
    } else {
      gcd.data = alowbit;
      s = inverse_mod_2_k(a.data, __builtin_ctzll(alowbit));
      t.data = 0;
    }
  }

  /* returns unit and generator of annihilator ideal:
     a*unit is canonical (2^n) and a*annihilator=0 */
  inline friend void unit_annihilator(local2_small &unit, local2_small &annihilator, const local2_small &a) {
    if (a.data == 0) {
      unit.data = 0;
      annihilator.data = 1;
      return;
    }
    int shift = __builtin_ctzll(a.data);
    unit = inverse_mod_2_k(a.data, shift);
    if (shift == 0)
      annihilator.data = 0;
    else
      annihilator.data = 1ULL << (K-shift);
  }

  inline int out_str(FILE *f) const {
    return fprintf(f, "%" PRIu64, data); /* maybe we should print in binary or hex? */
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
    trio_sprintf(p, "%..*" PRIu64, base, data);
#ifdef __clang__
#pragma clang diagnostic pop
#elif defined(__GNUC__)
#pragma GCC diagnostic pop
#endif
#else
    sprintf(p, "%" PRIu64, data);
#endif
    if (s == nullptr)
      p = (char *) realloc(p, strlen(p)+1);

    return p;
  }

  /* conversions */
  //  template<unsigned L> inline void map(const localint<2,L> &a) { printf("yyy\n"); set_si(a.get_si()); } // !!! and kernel
};
