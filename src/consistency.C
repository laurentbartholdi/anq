/******************************************************************************
**
**                 Nilpotent Quotient for Lie Rings
** consistency.c                                                Csaba Schneider
**                                                           schcs@math.klte.hu
*/

#include "lienq.h"

/*
**  The goal of this file is to check the consistency relations in the
**  factorring.
*/

/*
**  CheckJacobi( a, b, c ) checks whether the Jacobi holds for
**  the triple ( a, b, c ) and returns its value in cv.
*/

/* cv += [[a,b],c] */
static void TripleProduct(coeffvec cv, gen a, gen b, gen c) {
  if (a < b) {
    for (gpvec p = Product[b][a]; p->g != EOW && p->g <= NrPcGens; p++)
      if (p->g > c)
	Diff(cv, p->c, Product[p->g][c]);
      else if (p->g < c)
	Sum(cv, p->c, Product[c][p->g]);
  } else {
    for (gpvec p = Product[a][b]; p->g != EOW && p->g <= NrPcGens; p++)
      if (p->g > c)
	Sum(cv, p->c, Product[p->g][c]);
      else if (p->g < c)
	Diff(cv, p->c, Product[c][p->g]);
  }
}

static void CheckJacobi(coeffvec cv, gen a, gen b, gen c) {
  if (Weight[a] + Weight[b] + Weight[c] > Class)
    return;

  ZeroCoeffVec(cv);	

  TripleProduct(cv, a, b, c);
  TripleProduct(cv, b, c, a);
  TripleProduct(cv, c, a, b);

  Collect(cv);

  if (Debug) {
    fprintf(OutputFile, "# consistency: [ %d, %d, %d ] = ", a, b, c);
    PrintCoeffVec(cv);
    fprintf(OutputFile, "\n");
  }
}

/*
**  The following function checks the consistency relation for
**  o_i[ a, b ] = [ (( o_ia )), b ] where (()) means the substitution
**  of the argument with its relation.
**
*/
static void CheckPower(coeffvec cv, gen a, gen b) {
  ZeroCoeffVec(cv);

  for (gpvec p = Power[a]; p->g <= NrPcGens && p->g != EOW; p++) {
    gen g = p->g;
    if (g > b)
      Diff(cv, p->c, Product[g][b]);
    else if (g < b)
      Sum(cv, p->c, Product[b][g]);
  }

  if (a > b)
    Sum(cv, Coefficients[a], Product[a][b]);
  else if (a < b)
    Diff(cv, Coefficients[a], Product[b][a]);

  Collect(cv);
  if (Debug) {
    fprintf(OutputFile, "# consistency %d %d: ", a, b);
    PrintCoeffVec(cv);
    fprintf(OutputFile, "\n");
  }
}

/*
**  The relations to be enforced are of form
**  [ a, b, c ] + [ b, c, a ] + [ c, a, b ]    where <a> is of weight 1
**  and  <a> < <b> < <c>  with respect to the linear ordering of the
**  generators.
*/

void Consistency() {
  coeffvec cv = NewCoeffVec();

  for (unsigned i = 1; i <= Dimensions[1]; i++)
    for (unsigned j = i + 1; j <= NrPcGens; j++)
      for (unsigned k = j + 1; k <= NrPcGens; k++) {
        CheckJacobi(cv, i, j, k);
	AddRow(cv);
      }

  for (unsigned i = 1; i <= NrPcGens; i++)
    if (coeff_nz(Coefficients[i]))
      for (unsigned j = 1; j <= NrPcGens; j++) {
        CheckPower(cv, i, j);
        AddRow(cv);
      }
  FreeCoeffVec(cv);

  if (Debug)
    fprintf(OutputFile, "# Consistency() finished\n");
}

void GradedConsistency() {
  coeffvec cv = NewCoeffVec();

  for (unsigned a = 1; a <= Dimensions[1]; a++)  /* a is of weight 1 */
    for (unsigned bw = 1; bw <= Class / 2; bw++) /* bw is the weight of b */
    {
      unsigned lwbdb, cw = Class - 1 - bw; /* the weight of c */
      SUM(Dimensions, bw - 1, lwbdb);
      for (unsigned b = MAX(a + 1, lwbdb + 1); b <= lwbdb + Dimensions[bw]; b++) {
	unsigned lwbdc;
        SUM(Dimensions, cw - 1, lwbdc);
        for (unsigned c = MAX(b + 1, lwbdc + 1); c <= lwbdc + Dimensions[cw]; c++) {
	  CheckJacobi(cv, a, b, c);
	  AddRow(cv);
        }
      }
    }

  for (unsigned aw = 1; aw <= Class - 1; aw++) /* the grade of a */
  {
    unsigned lwbda, lwbdb, bw = Class - aw; /* that of b */
    SUM(Dimensions, aw - 1, lwbda);
    SUM(Dimensions, bw - 1, lwbdb);
    for (unsigned a = lwbda + 1; a <= lwbda + Dimensions[aw]; a++)
      if (coeff_nz(Coefficients[a]))
        for (unsigned b = lwbdb + 1; b <= lwbdb + Dimensions[bw]; b++) {
	  CheckPower(cv, a, b);
	  AddRow(cv);
        }
  }
  FreeCoeffVec(cv);

  if (Debug)
    fprintf(OutputFile, "# GradedConsistency() finished.\n");
}
