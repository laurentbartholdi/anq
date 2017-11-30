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

/* v += [[a,b],c] */
void TripleProduct(gpvec &v, gen a, gen b, gen c) {
  gpvec temp[2];
  temp[0] = FreshVec();
  temp[1] = FreshVec();
  bool parity = false;
  
  if (a < b) {
    for (gpvec p = Product[b][a]; p->g != EOW && p->g <= NrPcGens; p++)
      if (p->g > c)
	Diff(temp[!parity], temp[parity], p->c, Product[p->g][c]), parity ^= 1;
      else if (p->g < c)
	Sum(temp[!parity], temp[parity], p->c, Product[c][p->g]), parity ^= 1;
  } else {
    for (gpvec p = Product[a][b]; p->g != EOW && p->g <= NrPcGens; p++)
      if (p->g > c)
	Sum(temp[!parity], temp[parity], p->c, Product[p->g][c]), parity ^= 1;
      else if (p->g < c)
	Diff(temp[!parity], temp[parity], p->c, Product[c][p->g]), parity ^= 1;
  }
#if 0
  if (parity)
    PopVec(v), PopVec();
  else
    PopVec(), PopVec(v);
#else
  Copy(v, temp[parity]);
  PopVec();
  PopVec();
#endif
}

static void CheckJacobi(gpvec v, gen a, gen b, gen c) {
  if (Weight[a] + Weight[b] + Weight[c] > Class)
    return;

  gpvec temp1 = FreshVec();
  gpvec temp2 = FreshVec();
  gpvec temp3 = FreshVec();
  TripleProduct(temp1, a, b, c);
  TripleProduct(temp2, b, c, a);
  TripleProduct(temp3, c, a, b);
  Sum(v, temp1, temp3);
  Sum(temp3, v, temp2);
  Collect(v, temp3);

  PopVec();
  PopVec();
  PopVec();

  if (Debug) {
    fprintf(OutputFile, "# consistency: [ %d, %d, %d ] = ", a, b, c);
    PrintVec(v);
    fprintf(OutputFile, "\n");
  }
}

/*
**  The following function checks the consistency relation for
**  o_i[ a, b ] = [ (( o_ia )), b ] where (()) means the substitution
**  of the argument with its relation.
**
*/
static void CheckPower(gpvec v, gen a, gen b) {
  gpvec temp[2];
  temp[0] = FreshVec();
  temp[1] = FreshVec();
  bool parity = false;
  
  for (gpvec p = Power[a]; p->g <= NrPcGens && p->g != EOW; p++) {
    gen g = p->g;
    if (g > b)
      Diff(temp[!parity], temp[parity], p->c, Product[g][b]), parity ^= 1;
    else if (g < b)
      Sum(temp[!parity], temp[parity], p->c, Product[b][g]), parity ^= 1;
  }

  if (a > b)
    Sum(temp[!parity], temp[parity], Coefficients[a], Product[a][b]), parity ^= 1;
  else if (a < b)
    Diff(temp[!parity], temp[parity], Coefficients[a], Product[b][a]), parity ^= 1;
  Collect(v, temp[parity]);

  PopVec();
  PopVec();
  
  if (Debug) {
    fprintf(OutputFile, "# consistency %d %d: ", a, b);
    PrintVec(v);
    fprintf(OutputFile, "\n");
  }
}

/*
**  The relations to be enforced are of form
**  [ a, b, c ] + [ b, c, a ] + [ c, a, b ]    where <a> is of weight 1
**  and  <a> < <b> < <c>  with respect to the linear ordering of the
**  generators.
*/

void Consistency(void) {
  for (unsigned i = 1; i <= Dimensions[1]; i++)
    for (unsigned j = i + 1; j <= NrPcGens; j++)
      for (unsigned k = j + 1; k <= NrPcGens; k++) {
	gpvec v = FreshVec();
        CheckJacobi(v, i, j, k);
	AddRow(v);
	PopVec();
      }

  for (unsigned i = 1; i <= NrPcGens; i++)
    if (coeff_nz(Coefficients[i]))
      for (unsigned j = 1; j <= NrPcGens; j++) {
	gpvec v = FreshVec();
        CheckPower(v, i, j);
        AddRow(v);
	PopVec();
      }

  if (Debug)
    fprintf(OutputFile, "# Consistency() finished\n");
}

void GradedConsistency(void) {
  for (unsigned a = 1; a <= Dimensions[1]; a++)  /* a is of weight 1 */
    for (unsigned bw = 1; bw <= Class / 2; bw++) /* bw is the weight of b */
    {
      unsigned lwbdb, cw = Class - 1 - bw; /* the weight of c */
      SUM(Dimensions, bw - 1, lwbdb);
      for (unsigned b = MAX(a + 1, lwbdb + 1); b <= lwbdb + Dimensions[bw]; b++) {
	unsigned lwbdc;
        SUM(Dimensions, cw - 1, lwbdc);
        for (unsigned c = MAX(b + 1, lwbdc + 1); c <= lwbdc + Dimensions[cw]; c++) {
	  gpvec v = FreshVec();
	  CheckJacobi(v, a, b, c);
	  AddRow(v);
	  PopVec();
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
	  gpvec v = FreshVec();
	  CheckPower(v, a, b);
	  AddRow(v);
	  PopVec();
        }
  }

  if (Debug)
    fprintf(OutputFile, "# GradedConsistency() finished.\n");
}
