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

/****************************************************************
 * coefficients.
 * they can be of various types, with varying performance:
 * - signed long int
 * - multiprecision gmpz_t
 * - hybrid 63-bit signed long / gmpz_t
 * - mod-2^64 arithmetic (unsigned long int)
 * - mod-p^k arithmetic (unsigned long int)
 ****************************************************************/
#ifdef COEFF_IS_LONG
#include "coeff_long.h"
#elif defined(COEFF_IS_MPZ)
#include "coeff_mpz.h"
#elif defined(COEFF_IS_Z)
#include "coeff_z.h"
#elif defined(COEFF_IS_MOD2_64)
#include "coeff_2_64.h"
#elif defined(COEFF_IS_MODp_k)
#include "coeff_p_k.h"
#else
#error you must specify a coefficient type: COEFF_IS_LONG, ...
#include </> // force stop
#endif

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
  TNUM, TGEN, TMPROD, TLPROD, TSUM, TREL, TDRELL, TDRELR
};

struct node {
  nodetype type;
    
  union {
    coeff n;
    gen g;
    struct {
      node *l, *r;
    } op;
  } cont;
};

struct presentation {
  unsigned NrGens, NrRels, NrExtraRels;
  char **Generators;
  node **Relators;
  node **ExtraRelators;
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

/* useful macros */
#define MAX(x, y) ((x) < (y) ? (y) : (x))
#define SUM(a, n, s)                                                           \
  {									\
    unsigned i;								\
    for (i = 1, s = 0; i <= (n); s += a[i], i++)			\
      ;									\
  }

/****************************************************************
 * global variables dictating the behaviour of lienq
 ****************************************************************/
extern bool Graded, PrintZeros, PrintDefs;
extern unsigned Debug;
extern FILE *OutputFile;
extern unsigned Class;

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
extern clock_t ClockStart;
extern void abortprintf(int, const char *, ...) __attribute__((format(printf, 2, 3)));
void PrintVec(gpvec);
void PrintPcPres(void);
void TimeStamp(const char *);
  
/* presentation functions */
extern gpvec **Product, *Power, *Epimorphism;
extern coeff *Coefficients;
extern unsigned *Weight, *Dimensions;
extern deftype *Definitions;
extern unsigned NrPcGens, NrCenGens, NrTotalGens;

void InitPcPres(void);
void FreePcPres(void);
void EvalAllRel(void);
unsigned ReducedPcPres(void);
void ExtendPcPres(void);

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
  if (coeff_nz(n))
    for (; vec->g != EOW; vec++) {
      coeff_mul(vec0->c, vec->c, n);
      if (coeff_nz(vec0->c))
	vec0->g = vec->g, vec0++;
    }
  vec0->g = EOW;
}
inline void Neg(gpvec vec1, constgpvec vec2) {
  for (; vec2->g != EOW; vec1++, vec2++)
    coeff_neg(vec1->c, vec2->c), vec1->g = vec2->g;
  vec1->g = EOW;
}
void Prod(gpvec, constgpvec, constgpvec);
void Collect(gpvec, constgpvec);
void ShrinkCollect(gpvec &);

/* epim functions */
void InitEpim(void);
void FreeEpim(void);

/* readpres functions */
extern presentation Pres;

void ReadPresentation(const char *);
void FreePresentation(void);
void EvalRel(gpvec, node *);

/* addgen functions */
void AddGen(void);
void GradedAddGen(void);

/* matrix functions */
extern unsigned NrRows;
extern gpvec *Matrix;
void HermiteNormalForm(void);
bool AddRow(gpvec);
void InitMatrix(void);
void FreeMatrix(void);
