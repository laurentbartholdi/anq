/**************************************************************** nq.h
 * Nilpotent Quotient for Groups, Lie and Associative Algebras
 *
 * Based on code by Csaba Schneider, itself based on code from Werner
 * Nickel
 */

#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <vector>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include "ring.hh"
#include "vectors.hh"

/****************************************************************
 * the code will work for groups, Lie and associative algebras, with
 * different routines called for collection, enforcing consistency
 * etc.
 */
#ifdef LIEALG
#define LIEGPSTRING "Lie algebra"
#define INT_ASSOCALG 0
#elif defined(ASSOCALG)
#define LIEGPSTRING "associative algebra"
#define INT_ASSOCALG 1
#elif defined(GROUP)
#define LIEGPSTRING "group"
#define INT_ASSOCALG 0
#else
#error GROUP or LIEALG or ASSOCALG must be defined
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
 * there are 3 kinds of coefficients:
 * - pccoeff, used within pc presentations
 * - fpcoeff, used in the defining fp presentation
 * - matcoeff, used in matrix calculations involving the centre.
 *
 * all 3 can be different. e.g., to compute a 2-central series, one
 * would select pccoeff=fpcoeff=Z and matcoeff=Z/2.
 * to compute in a p-restricted Lie algebra, one would select fpcoeff=Z
 * and pccoeff=matcoeff=Z/p.
 *
 * generator-coefficient pairs are used for sparse vectors.  They
 * store structure constants and sparse matrix rows; never used for
 * calculations.
 */

#ifndef PCCOEFF_P
#define PCCOEFF_P 0
#endif
#ifndef PCCOEFF_K
#define PCCOEFF_K 1
#endif
#ifndef MATCOEFF_P
#define MATCOEFF_P PCCOEFF_P
#endif
#ifndef MATCOEFF_K
#define MATCOEFF_K PCCOEFF_K
#endif

#if PCCOEFF_P > 0 && (MATCOEFF_P != PCCOEFF_P || MATCOEFF_K > PCCOEFF_K)
#error Matrix coefficients are not a quotient of pc coefficients
#endif

typedef integer<PCCOEFF_P,PCCOEFF_K> pccoeff;
namespace std {
  template<> struct hash<pccoeff> : public pccoeff::hash { };
  template<> struct equal_to<pccoeff> : public pccoeff::equal_to { };
}

typedef sparsevec<pccoeff> sparsepcvec;
typedef sparsepcvec::key gen;
struct hollowpcvec;
typedef std::vector<sparsepcvec> sparsepcmat; // compressed rows
namespace std {
  template<> struct hash<sparsepcvec> : public sparsepcvec::hash { };
}

typedef pccoeff fpcoeff;

#if PCCOEFF_P != MATCOEFF_P || PCCOEFF_K != MATCOEFF_K
typedef integer<MATCOEFF_P,MATCOEFF_K> matcoeff;
template<> struct std::hash<matcoeff> : public matcoeff::hash { };
template<> struct std::equal_to<matcoeff> : public matcoeff::equal_to { };

typedef sparsevec<matcoeff> sparsematvec;
template<> struct std::hash<sparsematvec> : public sparsematvec::hash { };
typedef std::vector<sparsematvec> sparsematmat; // compressed rows

struct hollowmatvec : hollowvec<matcoeff> { };
template<> struct std::hash<hollowmatvec> : public hollowmatvec::hash { };

inline bool operator==(const sparsematvec &vec1, const sparsematvec &vec2) { return vec_equal(vec1, vec2); }
inline bool operator==(const sparsematvec &vec1, const hollowmatvec &vec2) { return vec_equal(vec1, vec2); }
inline bool operator==(const hollowmatvec &vec1, const sparsematvec &vec2) { return vec_equal(vec1, vec2); }
inline bool operator==(const hollowmatvec &vec1, const hollowmatvec &vec2) { return vec_equal(vec1, vec2); }
inline bool operator!=(const sparsematvec &vec1, const sparsematvec &vec2) { return !vec_equal(vec1, vec2); }
inline bool operator!=(const sparsematvec &vec1, const hollowmatvec &vec2) { return !vec_equal(vec1, vec2); }
inline bool operator!=(const hollowmatvec &vec1, const sparsematvec &vec2) { return !vec_equal(vec1, vec2); }
inline bool operator!=(const hollowmatvec &vec1, const hollowmatvec &vec2) { return !vec_equal(vec1, vec2); }
inline bool operator<(const sparsematvec &vec1, const sparsematvec &vec2) { return vec_cmp(vec1, vec2) < 0; }
inline bool operator<(const sparsematvec &vec1, const hollowmatvec &vec2) { return vec_cmp(vec1, vec2) < 0; }
inline bool operator<(const hollowmatvec &vec1, const sparsematvec &vec2) { return vec_cmp(vec1, vec2) < 0; }
inline bool operator<(const hollowmatvec &vec1, const hollowmatvec &vec2) { return vec_cmp(vec1, vec2) < 0; }
#else
typedef pccoeff matcoeff;
typedef sparsepcvec sparsematvec;
typedef hollowpcvec hollowmatvec;
typedef sparsepcmat sparsematmat;
#endif

/****************************************************************
 * matrix functions.
 * matrices are stored as std::vector<sparsecvec>
 * 
 * we implement Gaussian elimination, with no care in selecting the
 * best numerical values as pivots, but attempting to avoid too much
 * fill-in using colamd.
 */
class matrix {
  /* we maintain a square NrColsxNrCols matrix (with sparse rows)
     to store the current relations. If row Matrix[i] is allocated, then
     its pivot should be in position i+Shift; so the matrix
     really has (row,column)-space equal to
     [0,nrcols) x [shift,NrTotalGens].
  */
  const unsigned nrcols, shift;
  const bool torsionfree;
  sparsematmat rows;
  std::unordered_set<sparsematvec> queue;
  mutable vec_supply<hollowmatvec> rowstack;

  void inittorsion();
  bool add1row(hollowmatvec);
 public:
  matrix(unsigned, unsigned, bool);
  ~matrix();
  void queuerow(const hollowpcvec);
  bool addrow(hollowpcvec);
  sparsepcvec reducerow(const sparsepcvec &) const;
  void flushqueue();
  void hermite();
  sparsepcvec getrel(pccoeff &, gen) const;
};

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
  TBRACK, TBRACE, TMAP, TSPROD, TPROD, TQUO, TLQUO,
  TPOW, TCONJ, TSUM, TDIFF, TREL, TDREL, TDRELR,
  TNEG, TINV, TFROB
};
static const char *nodename[] __attribute__((unused)) = {
  "TNUM",
  "TGEN",
  "TBRACK","TBRACE","TMAP","TSPROD","TPROD","TQUO","TLQUO",
  "TPOW","TCONJ","TSUM","TDIFF","TREL","TDREL","TDRELR",
  "TNEG", "TINV", "TFROB"
};
const nodetype TINVALID = (nodetype) -1;
constexpr static bool is_unary(nodetype t) { return t >= TNEG && t <= TFROB; }
constexpr static bool is_binary(nodetype t) { return t >= TBRACK && t <= TDRELR; }

struct node {
  nodetype type;
    
  union {
    fpcoeff n;
    gen g;
    struct {
      node *l, *r;
    };
    node *u;
  };
  node(nodetype _type) : type(_type) { }
  node(nodetype _type, fpcoeff _n) : type(_type) { n.init_set(_n); }  
  node(nodetype _type, gen _g) : type(_type), g(_g) { }
  node(nodetype _type, node *_l, node *_r) : type(_type), l(_l), r(_r) { }
  node(nodetype _type, node *_u) : type(_type), u(_u) { }

  ~node() {
    switch (type) {
    case TGEN:
      break;
    case TNUM:
      n.clear();
      break;
    default:
      if (is_unary(type))
	delete u;
      else {
	delete l;
	delete r;
      }
    }
  }
};

struct fppresentation {
  unsigned NrGens;
  std::vector<unsigned> Weight;
  std::vector<std::string> GeneratorName;
  std::vector<node *> Relators, Aliases, Endomorphisms;

  explicit fppresentation(const char *, bool);
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
  DCOMM,  /* g is defined as commutator (or associative product) */
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
#ifdef ASSOCALG
  std::vector<std::vector<sparsepcvec>> Prod; // the commutators: [aj,ai] = ... for j>i
#else
  std::vector<std::vector<sparsepcvec>> Comm; // the commutators: [aj,ai] = ... for j>i
#endif
  std::vector<sparsepcvec> Power, // powers: Exponent[i]*ai = ...
    Epimorphism; // epimorphism from fppresentation: Epimorphism[xi] = ...
  std::vector<pccoeff> Exponent, // the Exponent[i]*ai in next class
    Annihilator; // Annihilator[i]*ai = 0 was enforced earlier
  std::vector<deftype> Generator; // Generator[i] defines ai in terms of previous aj
  unsigned Class, // current class
    NrPcGens; // number of ai in current consistent pc presentation
  std::vector<unsigned> LastGen; // last generator number of given weight
  bool Graded; // is it a graded Lie algebra?
#ifdef LIEALG
  bool Jacobson; // is the algebra restricted?
  const bool Jennings = false;
#else
  const bool Jacobson = false;
  bool Jennings; // do we compute the Jennings series?
#endif
  bool TorsionFree; // do we kill torsion in the centre?
  bool Metabelian; // is the algebra/group metabelian?
  unsigned NilpotencyClass; // commutators of longer length must die
  
  explicit pcpresentation(const fppresentation &);
  ~pcpresentation();

  unsigned addtails();
  void consistency(matrix &) const;
  void evalrels(matrix &);
  void reduce(const matrix &);
  void print(FILE *f, bool, bool, bool) const;
  void printGAP(FILE *f) const;
private:
  void add1generator(sparsepcvec &, deftype);
  inline bool isgoodweight_comm(int i, int j) const;
  void collecttail(sparsepcvec &, const matrix &m, std::vector<int>);
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
 * we implement here some pcpresentation-specific operations.
 */
struct hollowpcvec : hollowvec<pccoeff> {
  void eval(const pcpresentation &, node *);
  void collect(const pcpresentation &);

  // functions for Lie algebras
#ifdef LIEALG
  void liebracket(const pcpresentation &, const hollowpcvec, const hollowpcvec); // this += [v,w]
  void lie3bracket(const pcpresentation &, gen, gen, gen, bool); // this (+/-)= [[v,w],x]
  void engel(const pcpresentation &, gen, gen, unsigned, bool); // this (+/-)= [u,v...,v]
  void frobenius(const pcpresentation &, const hollowpcvec);
#elif defined(GROUP)
  // functions for groups
  void collect(const pcpresentation &, gen, const pccoeff *c = nullptr); // collect one; last==nullptr means "1"

  void mul(const pcpresentation &pc, gen g, const pccoeff &c) { // this *= g^c
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

  template <typename V> void pow(const pcpresentation &, const V, const pccoeff &); // this *= v^n
  void lquo(const pcpresentation &, hollowpcvec, const hollowpcvec); // this *= v^-1 w
  template <typename V> void div(const pcpresentation &, const V); // this *= v^-1
#elif defined(ASSOCALG)
  void assocprod(const pcpresentation &, const hollowpcvec, const hollowpcvec, bool add = true); // this += v*w
  template <typename V> void assocprod(const pcpresentation &, gen, const V, bool add = true); // this += v*w
  template <typename V> void assocprod(const pcpresentation &, const V, gen, bool add = true); // this += v*w
  void pow(const pcpresentation &, int); // this ^= n
#endif
};

// a global stack to supply with very low overhead a fresh vector
extern vec_supply<hollowpcvec> vecstack;

inline bool operator==(const sparsepcvec &vec1, const sparsepcvec &vec2) { return vec_equal(vec1, vec2); }
inline bool operator==(const sparsepcvec &vec1, const hollowpcvec &vec2) { return vec_equal(vec1, vec2); }
inline bool operator==(const hollowpcvec &vec1, const sparsepcvec &vec2) { return vec_equal(vec1, vec2); }
inline bool operator==(const hollowpcvec &vec1, const hollowpcvec &vec2) { return vec_equal(vec1, vec2); }
inline bool operator!=(const sparsepcvec &vec1, const sparsepcvec &vec2) { return !vec_equal(vec1, vec2); }
inline bool operator!=(const sparsepcvec &vec1, const hollowpcvec &vec2) { return !vec_equal(vec1, vec2); }
inline bool operator!=(const hollowpcvec &vec1, const sparsepcvec &vec2) { return !vec_equal(vec1, vec2); }
inline bool operator!=(const hollowpcvec &vec1, const hollowpcvec &vec2) { return !vec_equal(vec1, vec2); }
inline bool operator<(const sparsepcvec &vec1, const sparsepcvec &vec2) { return vec_cmp(vec1, vec2) < 0; }
inline bool operator<(const sparsepcvec &vec1, const hollowpcvec &vec2) { return vec_cmp(vec1, vec2) < 0; }
inline bool operator<(const hollowpcvec &vec1, const sparsepcvec &vec2) { return vec_cmp(vec1, vec2) < 0; }
inline bool operator<(const hollowpcvec &vec1, const hollowpcvec &vec2) { return vec_cmp(vec1, vec2) < 0; }

namespace std {
  template<> struct hash<hollowpcvec> : public hollowpcvec::hash { };
}

#ifndef NO_TRIO
#include <trio.h>
#define printf trio_printf
#define sprintf trio_sprintf
#define fprintf trio_fprintf
#define PRIpccoeff "$<c%p:>"
#define PRIfpcoeff "$<c%p:>"
#define PRIsparsepcvec "$<s%p:>"
#define PRIsparsematvec "$<m%p:>"
#define PRIhollowpcvec "$<h%p:>"
#endif
