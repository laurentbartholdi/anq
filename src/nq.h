/**************************************************************** nq.h
 * Nilpotent Quotient for Groups and Lie Algebras
 *
 * Based on code by Csaba Schneider
 */

#ifndef NO_TRIO
#include <trio.h>
#define printf trio_printf
#define sprintf trio_sprintf
#define fprintf trio_fprintf
#define PRIcoeff "$<c%p:>"
#define PRIsparsecvec "$<s%p:>"
#define PRIhollowcvec "$<h%p:>"
#endif

#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <vector>
#include <string>
#include <unordered_map>
#include "ring.hh"
#include "vectors.hh"

typedef integer<0,1> coeff;

/****************************************************************
 * the code will work for groups and Lie algebras, with different
 * routines called for collection, enforcing consistency etc.
 */
#ifdef LIEALG
#define LIEGPSTRING "Lie algebra"
#elif defined(GROUP)
#define LIEGPSTRING "group"
#else
#error GROUP or LIEALG must be defined
#include /abort
#endif

inline const char *ordinal(unsigned n) {
  if (n % 10 == 1 && n != 11) return "st";
  if (n % 10 == 2 && n != 12) return "nd";
  if (n % 10 == 3 && n != 13) return "rd";
  return "th";
}

inline const char *plural(unsigned n) {
  return n == 1 ? "" : "s";
}

// some global variables dictating the behaviour of nq; in particular,
// the debug level and printing and timestamp routines

extern unsigned Debug;
extern FILE *LogFile;
void abortprintf(int, const char *, ...) __attribute__((format(__printf__, 2, 3),noreturn));
void TimeStamp(const char *);

/****************************************************************
 * generator-coefficient pairs and vectors.
 * Used to store structure constants and sparse matrix rows;
 * never used for calculations.
 */

struct coeff_ops {
  static void init(coeff &c) { c.init(); }
  static void clear(coeff &c) { c.clear(); }
  static bool nz_p(const coeff &c) { return c.nz_p(); }
  static void set(coeff &c, const coeff &d) { c.set(d); }
  static void setzero(coeff &c) { c.zero(); }
};
typedef sparsevec<coeff,coeff_ops> sparsecvec;
typedef sparsecvec::key gen;
const gen LASTGEN = (gen) -1;

typedef std::vector<sparsecvec> sparsecmat; // compressed rows

/****************************************************************
 * groups and Lie algebras are input in the usual presentation
 * notation < generators | relations >. The expressions are encoded
 * as evaluation trees.
 *
 * they are parsed in fppresentation.cc and used in pcpresentation.cc.
 */
enum nodetype {
  TNUM,
  TGEN,
  TBRACK, TBRACE, TMAP, TPROD, TQUO, TLQUO, TPOW, TSUM, TDIFF, TREL, TDREL, TDRELR,
  TNEG, TINV, TFROB
};
static const char *nodename[] __attribute__((unused)) = {
  "TNUM",
  "TGEN",
  "TBRACK","TBRACE","TMAP","TPROD","TQUO","TLQUO","TPOW","TSUM","TDIFF","TREL","TDREL","TDRELR",
  "TNEG", "TINV", "TFROB"
};
const nodetype TINVALID = (nodetype) -1;
constexpr static bool is_unary(nodetype t) { return t >= TNEG && t <= TFROB; }
constexpr static bool is_binary(nodetype t) { return t >= TBRACK && t <= TDRELR; }

struct node {
  nodetype type;
    
  union {
    coeff n;
    gen g;
    struct {
      node *l, *r;
    };
    node *u;
  };
  node(nodetype _type) : type(_type) { }
  node(nodetype _type, coeff _n) : type(_type) { n.init_set(_n); }  
  node(nodetype _type, gen _g) : type(_type), g(_g) { }
  node(nodetype _type, node *_l, node *_r) : type(_type), l(_l), r(_r) { }
  node(nodetype _type, node *_u) : type(_type), u(_u) { }
};

struct fppresentation {
  unsigned NrGens;
  std::vector<unsigned> Weight;
  std::vector<std::string> GeneratorName;
  std::vector<node *> Relators, Aliases, Endomorphisms;

  explicit fppresentation(const char *);
  ~fppresentation();
  void printnode(FILE *f, const node *) const;
private:
  void printnodes(FILE *f, const node *n, nodetype t) const;
};

/****************************************************************
 * nilpotent quotients are computed via polycyclic presentations,
 * in struct pcpresentation.
 *
 * every pc generator x is defined as either
 * - an image of fp generator (then x = Epimorphism[g])
 * - an commutator of pc generators (then x = Comm[g][h])
 * - a power of a pc generator (then x = g^Exponent[g])
 */
const unsigned TEMPDEFMASK = 0x10;
enum gendeftype {
  DGEN,  /* g is defined as an image of original generator */
  DCOMM,  /* g is defined as commutator */
  DPOW, /* g is defined as power of a pc generator */
  TEMPGEN = DGEN | TEMPDEFMASK, // these temporary versions will be eliminated
  TEMPCOMM = DCOMM | TEMPDEFMASK, // by consistency and relations
  TEMPPOW = DPOW | TEMPDEFMASK,
};
  
struct deftype {
  gendeftype type;
  unsigned w, cw; // weight and commutator weight
  union {
    struct { gen g, h; }; // two arguments, for commutator
    gen s; // one argument, for epimorphism
    gen p; // one argument, for power
  };
};

struct pcpresentation {
  const fppresentation &fp;
  std::vector<std::vector<sparsecvec>> Comm; // the commutators: [aj,ai] = ... for j>i
  std::vector<sparsecvec> Power, // powers: Exponent[i]*ai = ...
    Epimorphism; // epimorphism from fppresentation: Epimorphism[xi] = ...
  std::vector<coeff> Exponent, // the Exponent[i]*ai in next class
    Annihilator; // Annihilator[i]*ai = 0 was enforced earlier
  std::vector<deftype> Generator; // Generator[i] defines ai in terms of previous aj
  unsigned Class, // current class
    NrPcGens; // number of ai in current consistent pc presentation
  std::vector<unsigned> LastGen; // last generator number of given weight
  bool Graded; // is it a graded Lie algebra?
  bool PAlgebra; // is it a p-Lie algebra/group?
  bool Jennings; // is the algebra restricted/the Jennings series?
  bool Metabelian; // is the algebra/group metabelian?
  coeff TorsionExp; // if PAlgebra, enforce TorsionExp*ai in next class
  unsigned NilpotencyClass; // commutators of longer length must die
  
  explicit pcpresentation(const fppresentation &);
  ~pcpresentation();

  unsigned addtails();
  void consistency() const;
  void evalrels();
  void reduce(const sparsecmat &);
  void print(FILE *f, bool, bool, bool) const;
  void printGAP(FILE *f) const;
private:
  void add1generator(sparsecvec &, deftype);
  inline bool isgoodweight_comm(int i, int j) const;
  void collecttail(const sparsecmat &, sparsecvec &, std::vector<int>);
  unsigned NrTotalGens; // number of current+tail ai in extended presentation
};

/****************************************************************
 * hollow vectors are a special kind of vector useful for temporaries
 * in sparse computations.
 * 
 * if an array has range 1..N and Z nonzeros, then we provide
 * - O(N) storage,
 * - O(1) access time on entries already visited
 * - O(1) access to previous and next nonzero entry, and in particular O(Z) traversal
 * - O(log (N/Z)) extra access time on first visit.
 *
 * we implement lots of arithmetic operations on these vectors, and
 * also more pcpresentation-specific ones.
 */
struct hollowcvec : hollowvec<coeff,coeff_ops> {
  template <typename V> inline void add(const V v) { // this += v
    for (const auto &kc : v)
      ::add((*this)[kc.first], (*this)[kc.first], kc.second);
  }
  template <typename V> inline void sub(const V v) { // this -= v
    for (const auto &kc : v)
      ::sub((*this)[kc.first], (*this)[kc.first], kc.second);
  }
  template <typename V> inline void addmul(const coeff &c, const V v) { // this += c*v
    for (const auto &kc : v)
      ::addmul((*this)[kc.first], c, kc.second);
  }
  template <typename V> inline void submul(const coeff &c, const V v) { // this -= c*v
    for (const auto &kc : v)
      ::submul((*this)[kc.first], c, kc.second);
  }
  inline void neg() {
    for (const auto &kc : *this)
      ::neg((*this)[kc.first], kc.second);
  }
  inline void mul(const coeff &c) {
    for (const auto &kc : *this)
      ::mul((*this)[kc.first], kc.second, c);
  }
    
  void eval(const pcpresentation &, node *);

  // functions for Lie algebras
  void liebracket(const pcpresentation &, const hollowcvec, const hollowcvec); // this += [v,w]
  void lie3bracket(const pcpresentation &, gen, gen, gen, bool); // this (+/-)= [[v,w],x]
  void frobenius(const pcpresentation &, const hollowcvec);
  void liecollect(const pcpresentation &);

  // functions for groups
  void collect(const pcpresentation &, gen, const coeff *c = nullptr); // collect one; last==nullptr means "1"

  void mul(const pcpresentation &pc, gen g, const coeff &c) { // this *= g^c
    if (c.z_p()) // easy peasy, but should not happen
      return;

    collect(pc, g, &c);
  }

  void mul(const pcpresentation &pc, gen g) { // this *= g
    collect(pc, g);
  }
  
  template <typename V> void mul(const pcpresentation &pc, const V v) { // this *= v
    for (const auto &kc : v)
      mul(pc, kc.first, kc.second);
  }

  template <typename V> void pow(const pcpresentation &, const V, const coeff &); // this *= v^n
  void lquo(const pcpresentation &, hollowcvec, const hollowcvec); // this *= v^-1 w
  template <typename V> void div(const pcpresentation &, const V); // this *= v^-1
};

template<> struct std::hash<coeff> {
  size_t operator()(const coeff &c) const { return c.hash(); }
};

template<> struct std::equal_to<coeff> {
  bool operator()(const coeff &c1, const coeff &c2) const {
    return !cmp(c1, c2);
  }   
};

template <typename V> struct hashvec {
  size_t operator()(V const& vec) const {
    size_t seed = vec.size();
    
    for(const auto &kc : vec) {
      seed ^= kc.first + 0x9e3779b9 + (seed << 6) + (seed >> 2);
      seed ^= std::hash<coeff>()(kc.second) + (seed << 6) + (seed >> 2);
    }
    
    return seed;
  }
};
template<> struct std::hash<sparsecvec> : public hashvec<sparsecvec> { };
template<> struct std::hash<hollowcvec> : public hashvec<hollowcvec> { };

template <typename V, typename W> bool vec_equal(const V &vec1, const W &vec2) {
  auto p1 = vec1.begin();
  auto p2 = vec2.begin();
  for (;;) {
    bool p1end = (p1 == vec1.end()), p2end = (p2 == vec2.end());
    if (p1end || p2end)
      return p1end == p2end;
    if (p1->first != p2->first)
      return false;
    if (cmp(p1->second, p2->second))
      return false;
    p1++; p2++;
  }
}
inline bool operator==(const sparsecvec &vec1, const sparsecvec &vec2) { return vec_equal(vec1, vec2); }
inline bool operator==(const sparsecvec &vec1, const hollowcvec &vec2) { return vec_equal(vec1, vec2); }
inline bool operator==(const hollowcvec &vec1, const sparsecvec &vec2) { return vec_equal(vec1, vec2); }
inline bool operator==(const hollowcvec &vec1, const hollowcvec &vec2) { return vec_equal(vec1, vec2); }
inline bool operator!=(const sparsecvec &vec1, const sparsecvec &vec2) { return !vec_equal(vec1, vec2); }
inline bool operator!=(const sparsecvec &vec1, const hollowcvec &vec2) { return !vec_equal(vec1, vec2); }
inline bool operator!=(const hollowcvec &vec1, const sparsecvec &vec2) { return !vec_equal(vec1, vec2); }
inline bool operator!=(const hollowcvec &vec1, const hollowcvec &vec2) { return !vec_equal(vec1, vec2); }

template <typename V, typename W> inline int vec_cmp(const V vec1, const W vec2) {
  auto p1 = vec1.begin();
  auto p2 = vec2.begin();
  for (;;) {
    bool p1end = (p1 == vec1.end()), p2end = (p2 == vec2.end());
    if (p1end || p2end)
      return p1end - p2end;
    if (p1->first != p2->first)
      return p1->first > p2->first ? 1 : -1;
    int c = cmp(p1->second, p2->second);
    if (c)
      return c;
    p1++; p2++;
  }
}

inline bool operator<(const sparsecvec &vec1, const sparsecvec &vec2) { return vec_cmp(vec1, vec2) < 0; }
inline bool operator<(const sparsecvec &vec1, const hollowcvec &vec2) { return vec_cmp(vec1, vec2) < 0; }
inline bool operator<(const hollowcvec &vec1, const sparsecvec &vec2) { return vec_cmp(vec1, vec2) < 0; }
inline bool operator<(const hollowcvec &vec1, const hollowcvec &vec2) { return vec_cmp(vec1, vec2) < 0; }

// a global stack to supply with very low overhead a fresh vector
extern vec_supply<hollowcvec> vecstack;

/****************************************************************
 * matrix functions.
 * matrices are stored as std::vector<sparsecvec>
 * 
 * we implement Gaussian elimination, with no care in selecting the
 * best numerical values as pivots, but attempting to avoid too much
 * fill-in using colamd.
 */
void InitMatrix(const coeff *, unsigned, unsigned);
void QueueInMatrix(const hollowcvec);
void FlushMatrixQueue();
void ReduceRow(hollowcvec &);
void Hermite();
void FreeMatrix();
bool AddToMatrix(const hollowcvec);
sparsecmat GetMatrix();
