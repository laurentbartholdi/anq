/******************************************************************************
**
**                  Nilpotent Quotient for Lie Rings
** tails.c                                                      Csaba Schneider
**                                                           schcs@math.klte.hu
*/

#include "lienq.h"

/*
**  Some of the newly introduced generators strictly depend on one another
**  hence we can compute them proceeding on an induction method.
**  The following couple of function stand for that staff.
*/

/*
**  The following function is for computing the tail of the
**  product [ a, b ] where "a" > "b" and "b" is of weight > 1. We
**  suppose that the tails for [ d, c ] are already computed where
**  "d" > "c" and "c" < "b" for all "d".
**  Hence [ a, b ] = [ a, g, h ] - [ a, h, g ] where "b" := [ g, h ]
**  is the definition of "b".
*/

static gpvec Tail_ab(gen a, gen b) {
  if (Weight[a] + Weight[b] > Class)
    return (gpvec)0;

  gpvec temp[3], cva = GenToGpVec(a), cvg = GenToGpVec(Definitions[b].g), cvh = GenToGpVec(Definitions[b].h);

  temp[0] = NewGpVec(NrTotalGens);
  temp[1] = NewGpVec(NrTotalGens);
  temp[2] = NewGpVec(NrTotalGens);
  Prod(temp[0], cva, cvg);
  Prod(temp[1], temp[0], cvh); /* temp[1] = [a,g,h] */
  Prod(temp[0], cva, cvh);
  Prod(temp[2], temp[0], cvg); /* temp[2] = [a,h,g] */
  Diff(temp[0], temp[1], temp[2]); /* temp[0] = [a,g,h] - [a,h,g] */

  if (Debug) {
    fprintf(OutputFile, "# tail: [ %d, %d ] = ", a, b);
    PrintGpVec(temp[0]);
    fprintf(OutputFile, "\n");
  }

  Collect(temp[1], temp[0]);
  
  free(temp[0]);
  free(temp[2]);
  free(cva);
  free(cvg);
  free(cvh);
  
  return temp[1];
}

void Tails() {
  gpvec tail;

  for (unsigned i = Dimensions[1] + 1; i <= NrPcGens; i++)
    for (unsigned j = i + 1; j <= NrPcGens; j++)
      if ((tail = Tail_ab(j, i)) != (gpvec)0) {
        unsigned l = Length(Product[j][i]);
        Product[j][i] = (gpvec) realloc(Product[j][i], (l + Length(tail) + 1) * sizeof(gpower));
        unsigned kk, k = 0;
        while (tail[k].g <= NrPcGens && tail[k].g != EOW)
          k++;

        for (kk = 0; tail[k + kk].g != EOW; kk++) {
          Product[j][i][l + kk].g = tail[k + kk].g;
          coeff_set(Product[j][i][l + kk].c, tail[k + kk].c);
        }
        Product[j][i][l + kk].g = EOW;
        free(tail);
      }

  if (Debug)
    fprintf(OutputFile, "# Tails() finished\n");
}

void GradedTails() {
  unsigned lwbd, lwbd1, upbd, upbd1;
  gpvec tail;

  for (unsigned k = 2; k <= Class / 2; k++) {
    SUM(Dimensions, k - 1, lwbd);
    SUM(Dimensions, k, upbd);
    for (unsigned i = lwbd + 1; i <= upbd; i++) {
      SUM(Dimensions, Class - k - 1, lwbd1);
      SUM(Dimensions, Class - k, upbd1);
      for (unsigned j = MAX(i + 1, lwbd1 + 1); j <= upbd1; j++) {
        unsigned l = Length(Product[j][i]);
        tail = Tail_ab(j, i);
        Product[j][i] = (gpvec) realloc(Product[j][i], (l + Length(tail) + 1) * sizeof(gpower));
        for (unsigned m = 0; tail[m].g != EOW; m++) {
          Product[j][i][l + m].g = tail[m].g;
          coeff_set(Product[j][i][l + m].c, tail[m].c);
        }
        Product[j][i][l + Length(tail)].g = EOW;
        free(tail);
      }
    }
  }
  if (Debug)
    fprintf(OutputFile, "# GradedTails() finished.\n");
}
