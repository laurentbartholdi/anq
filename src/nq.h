/**************************************************************** nq.h
 * Nilpotent Quotient for Groups and Lie Algebras
 *
 * Based on code by Csaba Schneider
 */

#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include "coeff.h"
#include <vector>
#include <string>
#include "vectors.hh"

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

/****************************************************************
 * generator-coefficient pairs and vectors.
 * Used to store structure constants and sparse matrix rows;
 * never used for calculations.
 */
struct coeff_ops {
  static void init(coeff &c) { coeff_init(c); }
  static void clear(coeff &c) { coeff_clear(c); }
  static bool nz_p(const coeff &c) { return coeff_nz_p(c); }
  static void set(coeff &c, const coeff &d) { coeff_set(c,d); }
  static void setzero(coeff &c) { coeff_set_si(c,0); }
};
typedef sparsevec<coeff,coeff_ops> sparsecvec;
typedef sparsecvec::key gen;
const sparsecvec badsparsecvec((sparsecvec::slot *)0xff00ff00ff00ffLL);

typedef std::vector<sparsecvec> relmatrix;

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
  TNEG, TINV
};
static const char *nodename[] __attribute__((unused)) = {
  "TNUM",
  "TGEN",
  "TBRACK","TBRACE","TMAP","TPROD","TQUO","TLQUO","TPOW","TSUM","TDIFF","TREL","TDREL","TDRELR",
  "TNEG", "TINV"
};
const nodetype TINVALID = (nodetype) -1;
constexpr static bool is_unary(nodetype t) { return t >= TNEG && t <= TINV; }
constexpr static bool is_binary(nodetype t) { return t >= TBRACK && t <= TDRELR; }

struct node {
  nodetype type;
    
  union {
    coeff n;
    gen g;
    struct {
      node *l, *r;
    } bin;
    node *u;
  } cont;
};

struct fppresentation {
  unsigned NrGens;
  std::vector<unsigned> Weight;
  std::vector<std::string> GeneratorName;
  std::vector<node *> Relators, Aliases, Endomorphisms, Extra;
};

void ReadPresentation(fppresentation &, const char *);
void FreePresentation(fppresentation &);
void PrintNode(FILE *f, const fppresentation &, node *);

/****************************************************************
 * nilpotent quotients are computed via polycyclic presentations,
 * in struct pcpresentation.
 *
 * every pc generator x is defined as either
 * - an image of fp generator (then x = Epimorphism[g])
 * - an commutator of pc generators (then x = Comm[g][h])
 * - a power of a pc generator (then x = g^Exponent[g])
 */
enum gendeftype {
  DGEN,  /* g is defined as an image of original generator */
  DCOMM,  /* g is defined as commutator */
  DPOW, /* g is defined as power of a pc generator */
};
const gendeftype DINVALID = (gendeftype) -1;
  
struct deftype {
  gendeftype t; // type
  gen g, h; // arguments, at most two
  unsigned w, cw; // weight and commutator weight
};

struct pcpresentation {
  sparsecvec **Comm, // the commutators: [aj,ai] = ... for j>i
    *Power, // powers: Exponent[i]*ai = ...
    *Epimorphism; // epimorphism from fppresentation: Epimorphism[xi] = ...
  coeff *Exponent, // the Exponent[i]*ai in next class
    *Annihilator; // Annihilator[i]*ai = 0 was enforced earlier
  deftype *Generator; // Generator[i] defines ai in terms of previous aj
  unsigned Class, // current class
    NrPcGens; // number of ai in current consistent pc presentation
  bool Graded; // is it a graded Lie algebra?
  bool PAlgebra; // is it a p-Lie algebra?
  coeff TorsionExp; // if PAlgebra, enforce TorsionExp*ai in next class
  unsigned NilpotencyClass; // commutators of longer length must die
};

void InitPcPres(pcpresentation &, const fppresentation &, bool, bool, coeff &, unsigned);
void FreePcPres(pcpresentation &, const fppresentation &);
unsigned AddTails(pcpresentation &, const fppresentation &);
void Consistency(const pcpresentation &);
void ReducePcPres(pcpresentation &, const fppresentation &, const relmatrix &);

/****************************************************************
 * some global variables dictating the behaviour of nq; in particular,
 * the debug level and a global stack from which to fetch temporary
 * vectors.
 */
extern unsigned Debug;
extern FILE *LogFile;
const unsigned INFINITY = 999999999;

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
    for (auto kc : v)
      coeff_add((*this)[kc.first], (*this)[kc.first], kc.second);
  }
  template <typename V> inline void sub(const V v) { // this -= v
    for (auto kc : v)
      coeff_sub((*this)[kc.first], (*this)[kc.first], kc.second);
  }
  template <typename V> inline void addmul(const coeff &c, const V v) { // this += c*v
    for (auto kc : v)
      coeff_addmul((*this)[kc.first], c, kc.second);
  }
  template <typename V> inline void submul(const coeff &c, const V v) { // this -= c*v
    for (auto kc : v)
      coeff_submul((*this)[kc.first], c, kc.second);
  }
  inline void neg() {
    for (auto kc : *this)
      coeff_neg((*this)[kc.first], kc.second);
  }
  inline void mul(coeff &c) {
    for (auto kc : *this)
      coeff_mul((*this)[kc.first], kc.second, c);
  }
    
  void eval(const pcpresentation &, node *);

  // functions for Lie algebras
  void liebracket(const pcpresentation &, const hollowcvec, const hollowcvec); // this += [v,w]
  void lie3bracket(const pcpresentation &, gen, gen, gen, bool); // this (+/-)= [[v,w],x]
  void liecollect(const pcpresentation &);

  // functions for groups
  //  void mul(const pcpresentation &, const hollowcvec); // this *= v
  //void mul(const pcpresentation &, const sparsecvec); // this *= v
  template <typename V> void mul(const pcpresentation &, const V); // this *= v
  void mul(const pcpresentation &, gen g); // this *= g
  void mul(const pcpresentation &, gen g, const coeff &c); // this *= g^c
  void pow(const pcpresentation &, hollowcvec, const coeff &); // this *= v^n
  void lquo(const pcpresentation &, hollowcvec, const hollowcvec); // this = v^-1 w
  void inv(const pcpresentation &, hollowcvec); // this = v^-1
};

/****************************************************************
 * a stack to supply with very low overhead a fresh vector
 */
extern stack<hollowcvec> vecstack;

void EvalAllRel(const pcpresentation &, const fppresentation &);

template <typename V, typename W> inline int Compare(const V vec1, const W vec2) {
  auto p1 = vec1.begin(), p2 = vec2.begin();
  for (;;) {
    bool p1end = (p1 == vec1.end()), p2end = (p2 == vec2.end());
    if (p1end || p2end)
      return p1end - p2end;
    if (p1->first != p2->first)
      return p1->first > p2->first ? 1 : -1;
    int c = coeff_cmp(p1->second, p2->second);
    if (c)
      return c;
    p1++; p2++;
  }
}

template <typename T> inline void neg(sparsecvec &v, const T w) {
  auto i = v.begin();
  for (auto kc : w) {
    i->first = kc.first;
    coeff_neg(i->second, kc.second);
    i++;
  }
  i.markend();
}

/****************************************************************
 * print functions
 */
template <typename V> static void PrintVec(FILE *f, const V v) {
  bool first = true;
  for (auto kc : v) {
#ifdef LIEALG
    if (first) first = false; else fprintf(f, " + ");
    coeff_out_str(f, kc.second);
    fprintf(f, "*a%d", kc.first);
#else
    if (first) first = false; else fprintf(f, " * ");
    fprintf(f, "a%d^", kc.first);
    coeff_out_str(f, kc.second);
#endif
  }
}

void abortprintf(int, const char *, ...) __attribute__((format(printf, 2, 3),noreturn));
void PrintPcPres(FILE *f, const pcpresentation &, const fppresentation &, bool, bool, bool);
void PrintGAPPres(FILE *f, const pcpresentation &, const fppresentation &);
void TimeStamp(const char *);
  
/****************************************************************
 * matrix functions.
 * matrices are stored as std::vector<sparsecvec>
 * 
 * we implement Gaussian elimination, with no care in selecting the
 * best numerical values as pivots, but attempting to avoid too much
 * fill-in using colamd.
 */
relmatrix GetRelMatrix();
void QueueInRelMatrix(const hollowcvec);
bool AddToRelMatrix(const hollowcvec);
void FlushQueue();
void InitRelMatrix(const pcpresentation &, unsigned);
void FreeRelMatrix();
