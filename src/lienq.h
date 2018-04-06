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

/****************************************************************
 * generators
 ****************************************************************/
typedef unsigned gen;
const gen EOW = (gen) 0;

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
  TNEG, TINV,
  TINVALID
};
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
  unsigned NrGens, NrRels, NrDefs, NrExtra;
  char **GeneratorName;
  node **Relators, **Definitions, **Extra;
};

/****************************************************************
 * a definition of a generator is as a commutator [g,h].
 * the special case h=0 means that generator is defined as image
 * of presentation generator g.
 ****************************************************************/
struct deftype {
  gen g;
  gen h;
};

/****************************************************************
 * global variables dictating the behaviour of lienq
 ****************************************************************/
extern bool PrintZeros, Graded, Gap, PrintDefs;
extern unsigned Debug;
extern unsigned long TorsionExp;
extern FILE *OutputFile;

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
inline unsigned Length(gpvec vec) {
  unsigned l = 0;
  while (vec[l].g != EOW) l++;
  return l;
}
gpvec NewVec(unsigned);
void FreeVec(gpvec, unsigned);
void FreeVec(gpvec);
gpvec ResizeVec(gpvec, unsigned, unsigned);

/* tails functions */
void Tails(void);
void GradedTails(void);

/* consistency functions */
void TripleProduct(gpvec &, gen, gen, gen);
void Consistency(void);
void GradedConsistency(void);

/* print functions */
extern void abortprintf(int, const char *, ...) __attribute__((format(printf, 2, 3),noreturn));
void PrintVec(gpvec);
void PrintPcPres(presentation &);
void TimeStamp(const char *);
  
/* presentation functions */
extern gpvec **Product, *Power, *Epimorphism;
extern coeff *Exponent, *Annihilator;
extern deftype *Definition;
inline bool isimggen(gen g) { /* g is defined as an image of original generator */
  return Definition[g].h == 0 && 0 < (int) Definition[g].g;
}
inline bool ispowergen(gen g) { /* g is defined as power of a pc generator */
  return Definition[g].h == 0 && 0 > (int) Definition[g].g;
}
inline bool iscommgen(gen g) { /* g is defined as commutator */
  return Definition[g].h != 0;
}

extern unsigned *Weight, *LastGen;
extern unsigned Class,
  NrPcGens, // = LastGen[Class-1]
  NrCenGens, // = LastGen[Class]-LastGen[Class-1]
  NrTotalGens; // = LastGen[Class]

void InitPcPres(presentation &);
void FreePcPres(presentation &);
void EvalAllRel(presentation &);
unsigned ReducedPcPres(presentation &, gpvec *, unsigned);
void ExtendPcPres(void);
void AddGen(presentation &);

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
void Prod(gpvec, constgpvec, constgpvec);
void Collect(gpvec, constgpvec);
void ShrinkCollect(gpvec &);

/* readpres functions */
unsigned ReadPresentation(presentation &, const char *);
void FreePresentation(presentation &);
void EvalRel(gpvec, node *);
void PrintNode(node *);

/* matrix functions */
void HermiteNormalForm(gpvec **, unsigned *);
bool AddRow(gpvec);
void InitMatrix(void);
void FreeMatrix(void);
