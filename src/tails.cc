/******************************************************************************
**
**                  Nilpotent Quotient for Lie Rings
** tails.c                                                      Csaba Schneider
**                                                           schcs@math.klte.hu
*/

#include "lienq.h"
#include <algorithm>

/*
**  Some of the newly introduced generators strictly depend on one another
**  hence we can compute them proceeding on an induction method.
*/

/* compute the correct tail for [aj,ai]:
 *
 * - if i is defined as [g,h], compute [j,i] = [j,g,h]-[j,h,g]
 * - if i is defined as N*g, compute [j,i] = N*[j,g]
 * - if j is defined as N*g, compute [j,i] = N*[g,i] or -N*[i,g]
 */
bool AdjustTail(gen j, gen i) {
  if (i <= LastGen[1] && !ispowergen(j)) /* nothing to do, it's a fresh gen */
    return true;

  if (Weight[j] + Weight[i] > Class) /* the tail would go too far out */
    return true;

  gpvec tail = FreshVec();

  if (iscommgen(i)) { /* ai = [g,h] */
    gen g = Definition[i].g, h = Definition[i].h;

    gpvec agh = FreshVec();
    TripleProduct(agh, j, g, h);
    gpvec ahg = FreshVec();
    TripleProduct(ahg, j, h, g);
    gpvec v = FreshVec();
    Diff(v, agh, ahg);
    Collect(tail, v);
    PopVec();
    PopVec();
    PopVec();

    if (Debug >= 2)
      fprintf(OutputFile, "# tail: [a%d,a%d] = [a%d,[a%d,a%d]] = ", j, i, j, g, h);
  } else if (ispowergen(i)) { /* ai=N*g */
    gen g = -Definition[i].g;
    gpvec v = FreshVec();
    Prod(v, Exponent[g], Product[j][g]);
    Collect(tail, v);
    PopVec();

    if (Debug >= 2) {
      fprintf(OutputFile, "# tail: [a%d,a%d] = ", j, i);
      coeff_out_str(OutputFile, Exponent[g]);
      fprintf(OutputFile, "*[a%d,a%d] = ", j, g);
    }
  } else { /* aj = N*g */
    gen g = -Definition[j].g;
    gpvec v = FreshVec();
    if (g > i)
      Prod(v, Exponent[g], Product[g][i]);
    else if (g < i) {
      Prod(v, Exponent[g], Product[i][g]);
      Neg(v);
    }
    Collect(tail, v);
    PopVec();

    if (Debug >= 2) {
      fprintf(OutputFile, "# tail: [a%d,a%d] = ", j, i);
      coeff_out_str(OutputFile, Exponent[g]);
      fprintf(OutputFile, "*[a%d,a%d] = ", g, i);
    }
  }

  if (Debug >= 2) {
    PrintVec(tail);
    fprintf(OutputFile, "\n");
  }

  unsigned k;
  for (k = 0; Product[j][i][k].g != EOW; k++)
    if (Product[j][i][k].g != tail[k].g || coeff_cmp(Product[j][i][k].c,tail[k].c))
      return false;

  if (tail[k].g != EOW) {
    Product[j][i] = ResizeVec(Product[j][i], k, Length(tail));
    Copy(Product[j][i]+k, tail+k);
  }

  PopVec(); /* tail */
  return true;
}

void Tails(void) {
  for (unsigned i = 1; i <= NrPcGens; i++) {
    for (unsigned j = i + 1; j <= NrPcGens; j++) {
      if (Graded && Weight[i]+Weight[j] != Class)
	continue;

      if (!AdjustTail(j, i))
	abortprintf(5, "Adjustment to tail of [a%d,a%d] doesn't lie in centre", j, i);
    }
  }
  
  TimeStamp("Tails()");
}
