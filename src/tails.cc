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
**  hence we can compute them inductively.
*/

/* compute the correct tail for [aj,ai]:
 *
 * - if i is defined as [g,h], compute [j,i] = [j,g,h]-[j,h,g]
 * - if i is defined as N*g, compute [j,i] = N*[j,g]
 * - if j is defined as N*g, compute [j,i] = N*[g,i] or -N*[i,g]
 */
static bool AdjustTail(pcpresentation &pc, gen j, gen i) {
  if (pc.Definition[i].t == DGEN && pc.Definition[j].t != DPOW) /* nothing to do, [aj,ai] is a defining generator */
    return true;

  gpvec tail = FreshVec();

  if (pc.Definition[i].t == DCOMM) { /* ai = [g,h] */
    gen g = pc.Definition[i].g, h = pc.Definition[i].h;

    gpvec agh = FreshVec();
    TripleProduct(pc, agh, j, g, h);
    gpvec ahg = FreshVec();
    TripleProduct(pc, ahg, j, h, g);
    gpvec v = FreshVec();
    Diff(v, agh, ahg);
    Collect(pc, tail, v);
    PopVec();
    PopVec();
    PopVec();

    if (Debug >= 2)
      fprintf(LogFile, "# tail: [a%d,a%d] = [a%d,[a%d,a%d]] = ", j, i, j, g, h);
  } else if (pc.Definition[i].t == DPOW) { /* ai=N*g */
    gen g = pc.Definition[i].g;
    gpvec v = FreshVec();
    Prod(v, pc.Exponent[g], pc.Product[j][g]);
    Collect(pc, tail, v);
    PopVec();

    if (Debug >= 2) {
      fprintf(LogFile, "# tail: [a%d,a%d] = ", j, i);
      coeff_out_str(LogFile, pc.Exponent[g]);
      fprintf(LogFile, "*[a%d,a%d] = ", j, g);
    }
  } else { /* aj = N*g */
    gen g = pc.Definition[j].g;
    gpvec v = FreshVec();
    if (g > i)
      Prod(v, pc.Exponent[g], pc.Product[g][i]);
    else if (g < i) {
      Prod(v, pc.Exponent[g], pc.Product[i][g]);
      Neg(v);
    }
    Collect(pc, tail, v);
    PopVec();

    if (Debug >= 2) {
      fprintf(LogFile, "# tail: [a%d,a%d] = ", j, i);
      coeff_out_str(LogFile, pc.Exponent[g]);
      fprintf(LogFile, "*[a%d,a%d] = ", g, i);
    }
  }

  if (Debug >= 2) {
    PrintVec(LogFile, tail);
    fprintf(LogFile, "\n");
  }

  unsigned k;
  for (k = 0; pc.Product[j][i][k].g != EOW; k++)
    if (pc.Product[j][i][k].g != tail[k].g || coeff_cmp(pc.Product[j][i][k].c,tail[k].c))
      return false;

  if (tail[k].g != EOW) {
    pc.Product[j][i] = ResizeVec(pc.Product[j][i], k, Length(tail));
    Copy(pc.Product[j][i]+k, tail+k);
  }

  PopVec(); /* tail */
  return true;
}

void ComputeTails(pcpresentation &pc) {
  for (unsigned i = 1; i <= pc.NrPcGens; i++) {
    for (unsigned j = i + 1; j <= pc.NrPcGens; j++) {
      unsigned totalweight = pc.Weight[i]+pc.Weight[j];
      if (totalweight > pc.Class || (pc.Graded && totalweight != pc.Class))
	continue;
      
      if (!AdjustTail(pc, j, i))
	abortprintf(5, "Adjustment to tail of [a%d,a%d] doesn't lie in centre", j, i);
    }
  }
  
  TimeStamp("Tails()");
}
