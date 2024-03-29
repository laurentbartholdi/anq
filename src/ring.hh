/****************************************************************
 * a simple arithmetic interface.
 * for P a prime:
 * integer<P,K> represents integers mod P^K.
 * implements init(), clear(),
 * add, sub, mul, fdiv, ... similarly to gmp interface.
 * uses Montgomery division-free algorithms.
 * for P=0:
 * integer<0,K> represents integers with K limbs.
 * K=1 is optimized (as good as int64_t) and K=0 is gmp's mpz_t.
 ****************************************************************/
#include <type_traits>
#include <utility>
#include <stdexcept>
#include <inttypes.h>
#include <ctype.h>
#include <gmp.h>
#include <string.h>
#include <stdlib.h>

#if GMP_LIMB_BITS != 64
#error I only considered this code on 64-bit systems
#endif

template<uint64_t P, unsigned K> struct integer;
template<unsigned K> class __ring0;
template<unsigned P> class __local2_small;
template<unsigned P> class __local2_big;
template<uint64_t P, unsigned K> class __localp_small;
template<uint64_t P, unsigned K> class __localp_big;

typedef __ring0<0> __ring0_mpz;
typedef __ring0<1> __ring0_64;
#include "r_int0.hh"
#include "r_int1.hh"
#include "r_intbig.hh"
#include "r_intmax.hh"
template<unsigned K=1> struct __intglobal : __ring0<K> {
  /* returns unit and generator of annihilator ideal:
     a*unit is canonical (>0 or power of P) and a*annihilator=0 */
  inline void inv(const __intglobal &a) {
    if (!a.cmp_si(1) || !a.cmp_si(-1))
      this->set(a);
    else
      throw std::runtime_error("inv() of non-invertible element");
  }

  inline friend void unit_annihilator(__intglobal *unit, __intglobal *annihilator, const __intglobal &a) {
    if (unit) unit->set_si(a.sgn());
    if (annihilator) annihilator->set_si(a.z_p());
  }

  inline unsigned val(const __intglobal &a) {
    throw std::runtime_error("val(): meaningless for global integers");
  }
    
  inline void shdivexact(const __intglobal &a, const __intglobal &b) {
    this->divexact(a, b);
  }

  inline void shdiv_q(const __intglobal &a, const __intglobal &b) {
    this->fdiv_q(a, b);
  }

  inline void shdiv_r(const __intglobal &a, const __intglobal &b) {
    this->fdiv_r(a, b);
  }

  inline friend uint64_t shdiv_ui(const __intglobal &a, uint64_t b) {
    return fdiv_ui(a, b);
  }

  inline uint64_t shdiv_q_ui(const __intglobal &a, uint64_t b) {
    return this->fdiv_q_ui(a, b);
  }

  inline uint64_t shdiv_r_ui(const __intglobal &a, uint64_t b) {
    return this->fdiv_r_ui(a, b);
  }

  inline friend void shdiv_qr(__intglobal &q, __intglobal &r, const __intglobal &a, const __intglobal &b) {
    fdiv_qr(q, r, a, b);
  }    

  inline friend uint64_t shdiv_qr_ui(__intglobal &q, __intglobal &r, const __intglobal &a, uint64_t b) {
    return fdiv_qr_ui(q, r, a, b);
  }
};

constexpr unsigned MAXK(uint64_t p) { return p <= 2 ? 64 : p <= 3 ? 40 : p <= 5 ? 27 : p <= 7 ? 22 : p <= 11 ? 18 : p <= 13 ? 17 : p <= 19 ? 15 : p <= 23 ? 14 : p <= 29 ? 13 : p <= 37 ? 12 : p <= 53 ? 11 : p <= 83 ? 10 : p <= 137 ? 9 : p <= 251 ? 8 : p <= 563 ? 7 : p <= 1621 ? 6 : p <= 7129 ? 5 : p <= 65521 ? 4 : p <= 2642239 ? 3 : p <= 4294967291LL ? 2 : p <= 18446744073709524983ULL ? 1 : 0; }

#include "r_2small.hh"
#include "r_2big.hh"
#include "r_psmall.hh"
#include "r_pbig.hh"

#if 0 // compiler produces just-as-good code with local2_small
template<> class __intlocal<2,64> {
  uint64_t data;
public:
};
#endif

template<unsigned K> struct __local2 : public std::conditional<K<=64,__local2_small<K>,__local2_big<K>>::type { };

template<uint64_t P, unsigned K> struct __localp : std::conditional<K<=MAXK(P),__localp_small<P,K>,__localp_big<P,K>>::type { };

template<uint64_t P, unsigned K> struct __intlocal : std::conditional<P==2,__local2<K>,__localp<P,K>>::type {
  inline void init() { }

  inline void init_set(const __intlocal &a) { this->set(a); }

  inline void init_set_si(int64_t a) { this->set_si(a); }

  inline void clear() { }

  inline void swap(__intlocal &b) {
    __intlocal tmp;
    tmp.set(*this);
    set(b);
    b.set(tmp);
  }
  
  inline void divexact(const __intlocal &a, const __intlocal &b) {
    fdiv_q(a, b);
  }
  
  inline void fdiv_q(const __intlocal &a, const __intlocal &b) {
    __intlocal r;
    fdiv_qr(*this, r, a, b);
  }

  inline void fdiv_r(const __intlocal &a, const __intlocal &b) {
    __intlocal q;
    fdiv_qr(q, *this, a, b);
  }

  inline friend uint64_t fdiv_ui(const __intlocal &a, uint64_t b) {
    __intlocal q, r;
    return fdiv_qr_ui(q, r, a, b);
  }

  inline uint64_t fdiv_q_ui(const __intlocal &a, uint64_t b) {
    __intlocal r;
    return fdiv_qr_ui(*this, r, a, b);
  }

  inline uint64_t fdiv_r_ui(const __intlocal &a, uint64_t b) {
    __intlocal q;
    return fdiv_qr_ui(q, *this, a, b);
  }
  
  /* these functions should be used when it is guaranteed that b is a power of characteristic */
  inline void shdivexact(const __intlocal &a, const __intlocal &b) {
    shdiv_q(a, b);
  }

  inline void shdiv_q(const __intlocal &a, const __intlocal &b) {
    __intlocal r;
    shdiv_qr(*this, r, a, b);
  }

  inline void shdiv_r(const __intlocal &a, const __intlocal &b) {
    __intlocal q;
    shdiv_qr(q, *this, a, b);
  }

  inline friend uint64_t shdiv_ui(const __intlocal &a, uint64_t b) {
    __intlocal q, r;
    return shdiv_qr_ui(q, r, a, b);
  }

  inline uint64_t shdiv_q_ui(const __intlocal &a, uint64_t b) {
    __intlocal r;
    return shdiv_qr_ui(*this, r, a, b);
  }

  inline uint64_t shdiv_r_ui(const __intlocal &a, uint64_t b) {
    __intlocal q;
    return shdiv_qr_ui(q, *this, a, b);
  }
};

template<uint64_t P=0, unsigned K=0> struct integer : std::conditional<P==0,__intglobal<K>,__intlocal<P,K>>::type {
  static const uint64_t characteristic = P;
  static const unsigned exponent = K;
  
  inline void set_str(const char *s, int base) {
    this->zero();

    if (*s == '0' && characteristic != 0) base = characteristic;
  
    while (isalnum(*s)) {
      this->mul_si(*this, base);
      this->add_si(*this, isdigit(*s) ? *s - '0' : *s + 10 - (isupper(*s) ? 'A' : 'a'));
      s++;
    }
  }
  
  inline void pow(const integer &a, int64_t b) {
    bool s = b < 0;
    if (s) b = -b;
    integer base;
    base.init_set(a);
    this->set_si(1);
    for(;;) {
      if (b & 1)
	this->mul(*this, base);
      b >>= 1;
      if (!b) break;
      base.mul(base, base);
    }
    if (s)
      this->inv(*this);
    base.clear();
  }

  // the kernel of the map integer<P,K> -> integer<Q,L>
  template<typename T> const void kernel() {
    if (0 > (int64_t) T::characteristic) {
      this->set_si(T::characteristic >> 1);
      this->mul_si(*this, 2);
      this->add_si(*this, T::characteristic & 1);
    } else
      this->set_si(T::characteristic);
    if (T::characteristic != 0)
      pow(*this, T::exponent);
  }
  
  explicit inline operator int64_t() const { return this->get_si(); }

  bool operator ==(const integer &a) const { return this->cmp(a) == 0; }
  bool operator !=(const integer &a) const { return this->cmp(a) != 0; }
  bool operator >(const integer &a) const { return this->cmp(a) > 0; }
  bool operator >=(const integer &a) const { return this->cmp(a) >= 0; }
  bool operator <(const integer &a) const { return this->cmp(a) < 0; }
  bool operator <=(const integer &a) const { return this->cmp(a) <= 0; }
  
  bool operator ==(int64_t a) const { return this->cmp_si(a) == 0; }
  bool operator !=(int64_t a) const { return this->cmp_si(a) != 0; }
  bool operator >(int64_t a) const { return this->cmp_si(a) > 0; }
  bool operator >=(int64_t a) const { return this->cmp_si(a) >= 0; }
  bool operator <(int64_t a) const { return this->cmp_si(a) < 0; }
  bool operator <=(int64_t a) const { return this->cmp_si(a) <= 0; }
  
  integer &operator +=(const std::pair<integer,integer> &a) { this->addmul(a.first,a.second); return *this; }
  integer &operator -=(const std::pair<integer,integer> &a) { this->submul(a.first,a.second); return *this; }

  integer &operator +=(const integer &a) { this->add(*this, a); return *this; }
  integer &operator -=(const integer &a) { this->sub(*this, a); return *this; }
  integer &operator *=(const integer &a) { this->mul(*this, a); return *this; }
  integer &operator /=(const integer &a) { this->fdiv_q(*this, a); return *this; }
  integer &operator %=(const integer &a) { this->fdiv_r(*this, a); return *this; }

  integer &operator +=(int64_t a) { this->add_si(*this, a); return *this; }
  integer &operator -=(int64_t a) { this->add_si(*this, -a); return *this; }
  integer &operator *=(int64_t a) { this->mul_si(*this, a); return *this; }
  integer &operator /=(int64_t a) { this->fdiv_ui(*this, a); return *this; }

  struct hash {
    size_t operator()(const integer &c) const { return c.hashkey(); }
  };

  struct equal_to {
    bool operator()(const integer &c1, const integer &c2) const {
      return !cmp(c1, c2);
    }
  };
};

template<uint64_t P, unsigned K> inline void init(integer<P,K> &a) { a.init(); }

template<uint64_t P, unsigned K> inline void init_set(integer<P,K> &a, const integer<P,K> &b) { return a.init_set(b); }

template<uint64_t P, unsigned K> inline void init_set_si(integer<P,K> &a, int64_t b) { return a.init_set_si(b); }

template<uint64_t P, unsigned K> inline void clear(integer<P,K> &a) { a.clear(); }

template<uint64_t P, unsigned K> inline bool z_p(const integer<P,K> &a) { return a.z_p(); }

template<uint64_t P, unsigned K> inline bool nz_p(const integer<P,K> &a) { return a.nz_p(); }

template<uint64_t P, unsigned K> inline bool reduced_p(const integer<P,K> &a, const integer<P,K> &b) { return a.reduced_p(b); }

template<uint64_t P, unsigned K> inline void set(integer<P,K> &result, const integer<P,K> &a) { result.set(a); }

template<uint64_t P, unsigned K> inline void set_si(integer<P,K> &result, int64_t a) { result.set_si(a); }

template<uint64_t P, unsigned K> inline int64_t get_si(const integer<P,K> &a) { return a.get_si(); }

template<uint64_t P, unsigned K> inline void zero(integer<P,K> &result) { result.zero(); }

template<uint64_t P, unsigned K> inline void add(integer<P,K> &result, const integer<P,K> &a, const integer<P,K> &b) { result.add(a, b); }

template<uint64_t P, unsigned K> inline void add_si(integer<P,K> &result, const integer<P,K> &a, int64_t b) { result.add_si(a, b); }

template<uint64_t P, unsigned K> inline void addmul(integer<P,K> &result, const integer<P,K> &a, const integer<P,K> &b) { result.addmul(a, b); }

template<uint64_t P, unsigned K> inline int cmp(const integer<P,K> &a, const integer<P,K> &b) { return a.cmp(b); }

template<uint64_t P, unsigned K> inline int cmp_si(const integer<P,K> &a, int64_t b) { return a.cmp_si(b); }

template<uint64_t P, unsigned K> inline void divexact(integer<P,K> &result, const integer<P,K> &a, const integer<P,K> &b) { result.divexact(a, b); }

template<uint64_t P, unsigned K> inline void fdiv_q(integer<P,K> &result, const integer<P,K> &a, const integer<P,K> &b) { result.fdiv_q(a, b); }

template<uint64_t P, unsigned K> inline void fdiv_r(integer<P,K> &result, const integer<P,K> &a, const integer<P,K> &b) { result.fdiv_r(a, b); }

template<uint64_t P, unsigned K> inline uint64_t fdiv_q_ui(integer<P,K> &result, const integer<P,K> &a, int64_t b) { return result.fdiv_q_ui(a, b); }

template<uint64_t P, unsigned K> inline void shdivexact(integer<P,K> &result, const integer<P,K> &a, const integer<P,K> &b) { result.shdivexact(a, b); }

template<uint64_t P, unsigned K> inline void shdiv_q(integer<P,K> &result, const integer<P,K> &a, const integer<P,K> &b) { result.shdiv_q(a, b); }

template<uint64_t P, unsigned K> inline void shdiv_r(integer<P,K> &result, const integer<P,K> &a, const integer<P,K> &b) { result.shdiv_r(a, b); }

template<uint64_t P, unsigned K> inline uint64_t shdiv_q_ui(integer<P,K> &result, const integer<P,K> &a, int64_t b) { return result.shdiv_q_ui(a, b); }

template<uint64_t P, unsigned K> inline void inv(integer<P,K> &result, const integer<P,K> &a) { result.inv(a); }

template<uint64_t P, unsigned K> inline void mul(integer<P,K> &result, const integer<P,K> &a, const integer<P,K> &b) { result.mul(a, b); }

template<uint64_t P, unsigned K> inline void mul_si(integer<P,K> &result, const integer<P,K> &a, int64_t b) { result.mul_si(a, b); }

template<uint64_t P, unsigned K> inline void neg(integer<P,K> &result, const integer<P,K> &a) { result.neg(a); }

template<uint64_t P, unsigned K> inline int sgn(const integer<P,K> &a) { return a.sgn(); }

template<uint64_t P, unsigned K> inline void sub(integer<P,K> &result, const integer<P,K> &a, const integer<P,K> &b) { result.sub(a, b); }

template<uint64_t P, unsigned K> inline void submul(integer<P,K> &result, const integer<P,K> &a, const integer<P,K> &b) { result.submul(a, b); }

template<uint64_t P, unsigned K> inline void swap(integer<P,K> &a, integer<P,K> &b) { a.swap(b); }

template<uint64_t P, unsigned K> inline int out_str(FILE *f, const integer<P,K> &a) { return a.out_str(f); }

template<uint64_t P, unsigned K> inline char *get_str(char *s, int len, int base, const integer<P,K> &a) { return a.get_str(s, len, base); }

template<uint64_t P, unsigned K> inline void set_str(integer<P,K> &a, const char *s, int base) { a.set_str(s, base); }

template<uint64_t P, unsigned K> inline void pow(integer<P,K> &result, const integer<P,K> &a, uint64_t b) { result.pow(a, b); }

template<uint64_t P, unsigned K, uint64_t Q, unsigned L> void map(integer<P,K> &a, const integer<Q,L> &b) {
  a.map(b);
}
