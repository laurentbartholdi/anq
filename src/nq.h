/******************************************************************************
**
**               Nilpotent Quotient for Groups and Lie Algebras
** lienq.h                                                      Csaba Schneider
**                                                           schcs@math.klte.hu
*/

#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include "coeff.h"
#include <vector>
#include <string>

#ifdef LIEALG
#define LIEGPSTRING "Lie algebra"
#elif defined(GROUP)
#define LIEGPSTRING "group"
#else
#error GROUP or LIEALG must be defined
#include /abort
#endif

const unsigned INFINITY = -1;

/****************************************************************
 * generators
 ****************************************************************/
//typedef unsigned gen;
//!!!const gen EOW = (gen) -1; // larger than all others

/****************************************************************
 * generator-coefficient pairs and vectors.
 * Used for structure constants and sparse matrix rows.
 ****************************************************************/
#include "vectors.hh"

struct coeff_sparseops {
  static void init(coeff &c) { coeff_init(c); }
  static void clear(coeff &c) { coeff_clear(c); }
  static bool nz_p(coeff &c) { return coeff_nz_p(c); }
  static void set(coeff &c, const coeff &d) { coeff_set(c,d); }
};
typedef sparsevec<coeff,coeff_sparseops> sparsecvec;
typedef sparsecvec::key gen;

typedef std::vector<sparsecvec> relmatrix;

/*
** An element in a lie-algebra is a sum of several multiplications. Hence it
** will be represented as a expresson-tree. For simplicity (from the user's
** point of view) wi allow four binary operations, i.e.: multiplying two
** generators (lie-product), adding two generators (w. r. t. the module),
** multiplying an integer and a generator (w. r. t. the module) and wi also
** allow the power of a generator to an integer exponent (lie-product).
*/
enum nodetype {
  TNUM,
  TGEN,
  TBRACK, TBRACE, TPROD, TQUO, TLQUO, TPOW, TSUM, TDIFF, TREL, TDREL, TDRELR,
  TNEG, TINV
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

struct presentation {
  unsigned NrGens;
  std::vector<unsigned> Weight;
  std::vector<std::string> GeneratorName;
  std::vector<node *> Relators, Aliases, Extra;
};

/****************************************************************
 * every pc generator x is defined as either
 * - an image of fp generator (then x = Epimorphism[g])
 * - an commutator of pc generators (then x = Product[g][h])
 * - a power of a pc generator (then x = g^Exponent[g])
 ****************************************************************/
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

/****************************************************************
 * global variables dictating the behaviour of lienq
 ****************************************************************/
extern unsigned Debug;
extern FILE *LogFile;

/* auxiliary functions */
void InitStack(void);
void FreeStack(void);
sparsecvec FreshVec(void);
void PopVec(void);
void PopVec(sparsecvec);

#if 0 //!!!
inline void Copy(sparsecvec vec1, const sparsecvec vec2) {
  auto p1 = vec1.begin();
  for (auto kc: vec2)
    coeff_set(p1->second, kc.second), p1->first = kc.first, p1++;
  p1.markend();
}
inline unsigned Length(const sparsecvec vec) {
  unsigned l = 0;
  for (auto gc __attribute__((unused)): vec) l++;
  return l;
}
sparsecvec NewVec(unsigned);
void FreeVec(sparsecvec, unsigned);
void FreeVec(sparsecvec);
sparsecvec ResizeVec(sparsecvec, unsigned, unsigned);
#endif

/* pcpresentation functions */
extern unsigned  NrTotalGens; // during extension of pc presentation, NrTotalGens = new NrPcGens

struct pcpresentation {
  sparsecvec **Product, // the Lie bracket: [aj,ai] = ...
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

void InitPcPres(pcpresentation &, const presentation &, bool, bool, coeff &, unsigned);
void FreePcPres(pcpresentation &, const presentation &);
void AddNewTails(pcpresentation &, const presentation &);
void ReducePcPres(pcpresentation &, const presentation &, const relmatrix &);

/* tails functions */
void ComputeTails(const pcpresentation &);

/* consistency functions */
void TripleProduct(const pcpresentation &, sparsecvec &, gen, gen, gen);
void Consistency(const pcpresentation &);

/* print functions */
void abortprintf(int, const char *, ...) __attribute__((format(printf, 2, 3),noreturn));
void PrintVec(FILE *f, const sparsecvec);
void PrintPcPres(FILE *f, const pcpresentation &, const presentation &, bool, bool, bool);
void PrintGAPPres(FILE *f, const pcpresentation &, const presentation &);
void TimeStamp(const char *);
  
/* operation functions */
void Sum(sparsecvec, const sparsecvec, const sparsecvec);
void Sum(sparsecvec, const sparsecvec, const coeff, const sparsecvec);
void Sum(sparsecvec, const coeff, const sparsecvec, const coeff, const sparsecvec);
void Diff(sparsecvec, const sparsecvec, const sparsecvec);
inline void Diff(sparsecvec vec0, const sparsecvec vec1, const coeff x2, const sparsecvec vec2) {
  coeff y2;
  coeff_init(y2);
  coeff_neg(y2, x2);
  Sum(vec0, vec1, y2, vec2);
  coeff_clear(y2);
}
inline void Diff(sparsecvec vec0, const coeff x1, const sparsecvec vec1, const coeff x2, const sparsecvec vec2) {
  coeff y2;
  coeff_init(y2);
  coeff_neg(y2, x2);
  Sum(vec0, x1, vec1, y2, vec2);
  coeff_clear(y2);
}
inline void Prod(sparsecvec vec0, const coeff n, const sparsecvec vec) {
  auto p0 = vec0.begin();
  if (coeff_nz_p(n))
    for (auto kc: vec) {
      coeff_mul(p0->second, kc.second, n);
      if (coeff_nz_p(p0->second))
	p0->first = kc.first, p0++;
    }
  p0.markend();
}
inline void Neg(sparsecvec vec1, const sparsecvec vec2) {
  auto p1 = vec1.begin();
  for (auto kc: vec2)
    coeff_neg(p1->second, kc.second), p1->first = kc.first, p1++;
  p1.markend();
}
inline void Neg(sparsecvec vec1) {
  for (auto kc: vec1)
    coeff_neg(kc.second, kc.second);
}
inline int Compare(const sparsecvec vec1, const sparsecvec vec2) {
  auto p1 = vec1.begin(), p2 = vec2.begin();
  for (;;) {
    if (p1->first != p2->first)
      return p1->first > p2->first ? 1 : -1;
    if (p1.atend())
      return 0;
    int c = coeff_cmp(p1->second, p2->second);
    if (c)
      return c;
    p1++; p2++;
  }
}
void LieBracket(const pcpresentation &, sparsecvec, const sparsecvec, const sparsecvec);
void GroupBracket(const pcpresentation &, sparsecvec, const sparsecvec, const sparsecvec);
void Prod(const pcpresentation &, sparsecvec, const sparsecvec, const sparsecvec);
void Conjugate(const pcpresentation &, sparsecvec, const sparsecvec, const sparsecvec);
void Quo(const pcpresentation &, sparsecvec, const sparsecvec, const sparsecvec);
void LQuo(const pcpresentation &, sparsecvec, const sparsecvec, const sparsecvec);
void Inv(const pcpresentation &, sparsecvec, const sparsecvec);
void Pow(const pcpresentation &, sparsecvec, const sparsecvec, coeff &);
void Collect(const pcpresentation &pc, sparsecvec, const sparsecvec);
void ShrinkCollect(const pcpresentation &pc, sparsecvec &);

/* fppresentation functions */
void ReadPresentation(presentation &, const char *);
void FreePresentation(presentation &);
void EvalRel(const pcpresentation &, sparsecvec, node *);
void EvalAllRel(const pcpresentation &, const presentation &);
void PrintNode(FILE *f, const presentation &, node *);

/* matrix functions */
relmatrix GetRelMatrix(void);
void AddToRelMatrix(const sparsecvec);
void InitRelMatrix(const pcpresentation &, unsigned);
void FreeRelMatrix(void);
