/******************************************************************************
**
**               Nilpotent Quotient for Lie Algebras
** lienq.h                                                      Csaba Schneider
**                                                           schcs@math.klte.hu
*/

#include <errno.h>
#include <stdio.h>
#include <stdlib.h>

/****************************************************************
 * generators
 ****************************************************************/
typedef unsigned gen;
const gen EOW = (gen) 0;

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
typedef coeff *coeffvec;

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
struct node {
  int type;
  union {
    coeff n;
    gen g;
    struct {
      node *l, *r;
    } op;
  } cont;
};

struct PresStruct {
  unsigned NrGens, NrRels, NrExtraRels;
  char **Generators;
  node **Relators;
  node **ExtraRelators;
};

/****************************************************************
 * a definition of a generator is as a commutator [g,h]
 ****************************************************************/
struct deftype {
  gen g;
  gen h;
};

/* useful macros */
#define MIN(x, y) ((x) > (y) ? (y) : (x))
#define MAX(x, y) ((x) < (y) ? (y) : (x))
#define SUM(a, n, s)                                                           \
  {                                                                            \
    unsigned i;                                                                     \
    for (i = 1, s = 0; i <= (n); s += a[i], i++)                               \
      ;                                                                        \
  }

/*  The following data structures contain the nilpotent presentation. */

extern gpvec **Product;
extern gpvec *Power;
extern coeffvec Coefficients;
extern gpvec *Epimorphism;

extern unsigned *Weight;
extern unsigned *Dimensions;

extern deftype *Definitions;

extern unsigned NrPcGens, NrCenGens, NrTotalGens;
extern unsigned Class;
extern PresStruct Pres;

/****************************************************************
 * global variables dictating the behaviour of lienq
 ****************************************************************/
extern bool Debug;
extern bool ZeroCenGens;
extern bool Graded;
extern bool PrintZeros;

extern FILE *InputFile;
extern char *InputFileName;

extern FILE *OutputFile;
extern char *OutputFileName;

/* auxialiary functions */
gpvec NewGpVec(unsigned);
void FreeGpVec(gpvec, unsigned);
void FreeGpVec(gpvec);
coeffvec NewCoeffVec(void);
void ZeroCoeffVec(coeffvec);
void FreeCoeffVec(coeffvec);
void CpVec(gpvec, constgpvec);
coeffvec GenToCoeffVec(gen);
gpvec GenToGpVec(gen);
unsigned Length(gpvec);
unsigned RealLength(coeffvec);
coeffvec GpVecToCoeffVec(constgpvec);
gpvec CoeffVecToGpVec(coeffvec);
void CoeffVecToGpVec(gpvec, coeffvec);
gpvec ShrinkGpVec(gpvec);

/* tails functions */
void Tails(void);
void GradedTails(void);

/* consistency functions */
void Consistency(void);
void GradedConsistency(void);

/* print functions */
void PrintPcPres(void);
void PrintEpim(void);
void PrintGpVec(gpvec);
void PrintCoeffVec(coeffvec);
void PrintMat(coeffvec *);
void PrintDefinitions(void);

/* presentation functions */
void InitPcPres(void);
void FreePcPres(void);
void ComputePcGen(gen, gen *, int);
void EvalAllRel(void);
void UpdatePcPres(void);
void ExtendPcPres(void);

/* operation functions */
void Sum(gpvec, constgpvec, constgpvec);
unsigned Sum(gpvec, constgpvec, const coeff, constgpvec);
void Sum(coeffvec, const coeff, constgpvec);
void Sum(coeffvec, constgpvec);
void Diff(gpvec, constgpvec, constgpvec);
unsigned Diff(gpvec, constgpvec, const coeff, constgpvec);
void Diff(coeffvec, const coeff, constgpvec);
void Diff(coeffvec, constgpvec);
void Prod(gpvec, constgpvec, constgpvec);
void ModProd(const coeff, gpvec);
void ModNeg(gpvec);
void Collect(coeffvec);
void Collect(gpvec, constgpvec);
void ShrinkCollect(gpvec &);

/* epim functions */
void InitEpim(void);
void FreeEpim(void);
gpvec Epim(gen);

/* readpres functions */
void ReadPresentation(void);
void FreePresentation(void);
void EvalRel(gpvec, node *);

/* addgen functions */
void AddGen(void);

/* matrix functions */
extern unsigned NrRows, NrCols, *Heads;
gpvec *MatrixToExpVecs(void);
bool AddRow(coeffvec);
void InitMatrix(void);
void FreeMatrix(void);
