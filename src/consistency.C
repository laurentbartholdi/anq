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
**  CheckZero( a, b, c ) checks whether the Jacobi holds for
**  the triple ( a, b, c ) and returns its value.
*/

static gpvec CheckZero(gen a, gen b, gen c)

{
  if (Weight[a] + Weight[b] + Weight[c] > Class)
    return (gpvec) 0;

  gpvec cva = GenToGpVec(a), cvb = GenToGpVec(b), cvc = GenToGpVec(c);

  gpvec p0 = NewGpVec(NrPcGens + NrCenGens);
  Prod(p0,cva,cvb);
  Prod(p0,p0,cvc); /* p0 = [[a,b],c] */

  gpvec p1 = NewGpVec(NrPcGens + NrCenGens);
  Prod(p1,cvb,cvc);
  Prod(p1,p1,cva); /* p1 = [[b,c],a] */

  gpvec p2 = NewGpVec(NrPcGens + NrCenGens);
  Sum(p2,p0,p1); /* p2 = [[a,b],c] + [[b,c],a] */

  Prod(p1,cvc,cva);
  Prod(p1,p1,cvb); /* p1 = [[c,a],b] */
  Sum(p0,p1,p2); /* p0 = Jacobi(a,b,c) */

  free(p1); free(p2); free(cva); free(cvb); free(cvc);

  if (Debug) {
    fprintf(OutputFile, "# consistency: [ %d, %d, %d ] = ", a, b, c);
    PrintGpVec(p0);
    fprintf(OutputFile, "\n");
  }
  return p0;
}

/*
**  The following function checks the consistency relation for
**  o_i[ a, b ] = [ (( o_ia )), b ] where (()) means the substitution
**  of the argument with its relation.
*/
static gpvec CheckPower(gen a, gen b) {
  gpvec temp[2];
  temp[0] = NewGpVec(NrPcGens + NrCenGens);
  temp[1] = NewGpVec(NrPcGens + NrCenGens);
  bool parity = 0;
  temp[0]->g = EOW;

  for (gpvec p = Power[a]; p->g <= NrPcGens && p->g != EOW; p++) {
    gen g = p->g;
    if (g > b)
      Sum(temp[!parity], temp[parity], -p->c, Product[g][b]), parity = !parity;
    else if (g < b)
      Sum(temp[!parity], temp[parity], p->c, Product[b][g]), parity = !parity;
  }

  if (a > b)
    Sum(temp[!parity], temp[parity], Coefficients[a], Product[a][b]), parity = !parity;
  else if (a < b)
    Sum(temp[!parity], temp[parity], -Coefficients[a], Product[b][a]), parity = !parity;

  Collect(temp[!parity], temp[parity]), parity = !parity;
  free (temp[!parity]);
  if (Debug) {
    fprintf(OutputFile, "# consistency %d %d: ", a, b);
    PrintGpVec(temp[parity]);
    fprintf(OutputFile, "\n");
  }
  return temp[parity];
}

/*
**  The relations to be enforced are of form
**  [ a, b, c ] + [ b, c, a ] + [ c, a, b ]    where <a> is of weight 1
**  and  <a> < <b> < <c>  with respect to the linear ordering of the
**  generators.
*/

void Consistency() {
  gpvec gv;

  for (unsigned i = 1; i <= Dimensions[1]; i++)
    for (unsigned j = i + 1; j <= NrPcGens; j++)
      for (unsigned k = j + 1; k <= NrPcGens; k++)
        if ((gv = CheckZero(i, j, k)) != (gpvec)0) {
          AddRow(gv);
	  free(gv);
        }

  for (unsigned i = 1; i <= NrPcGens; i++)
    if (Coefficients[i].notzero())
      for (unsigned j = 1; j <= NrPcGens; j++) {
        gv = CheckPower(i, j);
        AddRow(gv);
	free(gv);
      }
  if (Debug)
    fprintf(OutputFile, "# Consistency() finished\n");
}

void GradedConsistency() {
  unsigned lwbda, lwbdb, lwbdc;
  gpvec gv;

  for (unsigned a = 1; a <= Dimensions[1]; a++)  /* a is of weight 1 */
    for (unsigned bw = 1; bw <= Class / 2; bw++) /* bw is the weight of b */
    {
      unsigned cw = Class - 1 - bw; /* the weight of c */
      SUM(Dimensions, bw - 1, lwbdb);
      for (unsigned b = MAX(a + 1, lwbdb + 1); b <= lwbdb + Dimensions[bw]; b++) {
        SUM(Dimensions, cw - 1, lwbdc);
        for (unsigned c = MAX(b + 1, lwbdc + 1); c <= lwbdc + Dimensions[cw]; c++) {
          gv = CheckZero(a, b, c);
          AddRow(gv);
        }
      }
    }

  for (unsigned aw = 1; aw <= Class - 1; aw++) /* the grade of a */
  {
    unsigned bw = Class - aw; /* that of b */
    SUM(Dimensions, aw - 1, lwbda);
    SUM(Dimensions, bw - 1, lwbdb);
    for (unsigned a = lwbda + 1; a <= lwbda + Dimensions[aw]; a++)
      if (Coefficients[a].notzero())
        for (unsigned b = lwbdb + 1; b <= lwbdb + Dimensions[bw]; b++) {
          gv = CheckPower(a, b);
          AddRow(gv);
	  free(gv);
        }
  }

  if (Debug)
    fprintf(OutputFile, "# GradedConsistency() finished.\n");
}
