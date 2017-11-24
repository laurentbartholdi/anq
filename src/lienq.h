/******************************************************************************
**
**               Nilpotent Quotient for Lie Algebras
** lienq.h                                                      Csaba Schneider
**                                                           schcs@math.klte.hu
*/

#include "lietype.h"
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>

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

extern unsigned NrPcGens, NrCenGens;
extern unsigned Class;
extern PresStruct Pres;

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
coeffvec NewCoeffVec(void);
void CpVec(gpvec, gpvec);
void CpVecFree(gpvec, gpvec);
coeffvec GenToCoeffVec(gen);
gpvec GenToGpVec(gen);
unsigned Length(gpvec);
unsigned RealLength(coeffvec);
coeffvec GpVecToCoeffVec(gpvec);
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
void Sum(gpvec, gpvec, gpvec);
void Sum(gpvec, gpvec, coeff, gpvec);
void Prod(gpvec, gpvec, gpvec);
void ModProd(coeff, gpvec);
void ModNeg(gpvec);
gpvec Collect(gpvec);
void CollectCoeffVec(coeffvec);
void Collect(gpvec, gpvec);

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
bool AddRow(gpvec);
void InitMatrix(void);
void FreeMatrix(void);
