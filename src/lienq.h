/******************************************************************************
**
**               Nilpotent Quotient for Lie Algebras
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

const unsigned INFINITY = -1;

/****************************************************************
 * generators
 ****************************************************************/
typedef unsigned gen;
const gen EOW = (gen) -1; // larger than all others

/****************************************************************
 * generator-coefficient pairs and vectors.
 * Used for sparse matrix rows.
 ****************************************************************/
struct gpower {
  gen g;
  coeff c;
};
typedef gpower *gpvec;
typedef const gpower *constgpvec;

typedef std::vector<constgpvec> relmatrix;
  
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
  TBRACK, TBRACE, TPROD, TQUO, TPOW, TSUM, TDIFF, TREL, TDREL, TDRELR,
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
gpvec FreshVec(void);
void PopVec(void);
void PopVec(gpvec &);

inline void Copy(gpvec vec1, constgpvec vec2) {
  for (; vec2->g != EOW; vec1++, vec2++)
    coeff_set(vec1->c, vec2->c), vec1->g = vec2->g;
  vec1->g = EOW;
}
inline unsigned Length(constgpvec vec) {
  unsigned l = 0;
  while (vec[l].g != EOW) l++;
  return l;
}
gpvec NewVec(unsigned);
void FreeVec(gpvec, unsigned);
void FreeVec(gpvec);
gpvec ResizeVec(gpvec, unsigned, unsigned);

/* pcpresentation functions */
extern unsigned  NrTotalGens; // during extension of pc presentation, NrTotalGens = new NrPcGens

struct pcpresentation {
  gpvec **Product, // the Lie bracket: [aj,ai] = ...
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
void TripleProduct(const pcpresentation &, gpvec &, gen, gen, gen);
void Consistency(const pcpresentation &);

/* print functions */
void abortprintf(int, const char *, ...) __attribute__((format(printf, 2, 3),noreturn));
void PrintVec(FILE *f, constgpvec);
void PrintPcPres(FILE *f, const pcpresentation &, const presentation &, bool, bool, bool);
void PrintGAPPres(FILE *f, const pcpresentation &, const presentation &);
void TimeStamp(const char *);
  
/* operation functions */
void Sum(gpvec, constgpvec, constgpvec);
void Sum(gpvec, constgpvec, const coeff, constgpvec);
void Sum(gpvec, const coeff, constgpvec, const coeff, constgpvec);
void Diff(gpvec, constgpvec, constgpvec);
inline void Diff(gpvec vec0, constgpvec vec1, const coeff x2, constgpvec vec2) {
  coeff y2;
  coeff_init(y2);
  coeff_neg(y2, x2);
  Sum(vec0, vec1, y2, vec2);
  coeff_clear(y2);
}
inline void Diff(gpvec vec0, const coeff x1, constgpvec vec1, const coeff x2, constgpvec vec2) {
  coeff y2;
  coeff_init(y2);
  coeff_neg(y2, x2);
  Sum(vec0, x1, vec1, y2, vec2);
  coeff_clear(y2);
}
inline void Prod(gpvec vec0, const coeff n, constgpvec vec) {
  if (coeff_nz_p(n))
    for (; vec->g != EOW; vec++) {
      coeff_mul(vec0->c, vec->c, n);
      if (coeff_nz_p(vec0->c))
	vec0->g = vec->g, vec0++;
    }
  vec0->g = EOW;
}
inline void Neg(gpvec vec1, constgpvec vec2) {
  for (; vec2->g != EOW; vec1++, vec2++)
    coeff_neg(vec1->c, vec2->c), vec1->g = vec2->g;
  vec1->g = EOW;
}
inline void Neg(gpvec vec1) {
  for (; vec1->g != EOW; vec1++)
    coeff_neg(vec1->c, vec1->c);
}
inline int Compare(constgpvec vec1, constgpvec vec2) {
  for (;;) {
    if (vec1->g != vec2->g)
      return vec1->g > vec2->g ? 1 : -1;
    if (vec1->g == EOW)
      return 0;
    int c = coeff_cmp(vec1->c, vec2->c);
    if (c)
      return c;
    vec1++; vec2++;
  }
}
void LieBracket(const pcpresentation &pc, gpvec, constgpvec, constgpvec);
void Collect(const pcpresentation &pc, gpvec, constgpvec);
void ShrinkCollect(const pcpresentation &pc, gpvec &);

/* fppresentation functions */
void ReadPresentation(presentation &, const char *);
void FreePresentation(presentation &);
void EvalRel(const pcpresentation &, gpvec, node *);
void EvalAllRel(const pcpresentation &, const presentation &);
void PrintNode(FILE *f, const presentation &, node *);

/* matrix functions */
relmatrix GetRelMatrix(void);
void AddToRelMatrix(gpvec);
void InitRelMatrix(const pcpresentation &, unsigned);
void FreeRelMatrix(void);
