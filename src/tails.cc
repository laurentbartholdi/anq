/******************************************************************************
**
**                  Nilpotent Quotient for Lie Rings
** tails.c                                                      Csaba Schneider
**                                                           schcs@math.klte.hu
*/

#include "nq.h"
#include <algorithm>

/*
**  Some of the newly introduced generators strictly depend on one another
**  hence we can compute them inductively.
*/

// !!!GROUP

/* compute the correct tail for [aj,ai]:
 *
 * - if i is defined as [g,h], compute [j,i] = [j,g,h]-[j,h,g]
 * - if i is defined as N*g, compute [j,i] = N*[j,g]
 * - if j is defined as N*g, compute [j,i] = N*[g,i] or -N*[i,g]
 */
static bool AdjustTail(const pcpresentation &pc, gen j, gen i) {
  if (pc.Generator[i].t == DGEN && pc.Generator[j].t != DPOW) /* nothing to do, [aj,ai] is a defining generator */
    return true;

  sparsecvec tail = FreshVec();

  if (pc.Generator[i].t == DCOMM) { /* ai = [g,h] */
    gen g = pc.Generator[i].g, h = pc.Generator[i].h;

    sparsecvec agh = FreshVec();
    TripleProduct(pc, agh, j, g, h);
    sparsecvec ahg = FreshVec();
    TripleProduct(pc, ahg, j, h, g);
    sparsecvec v = FreshVec();
    Diff(v, agh, ahg);
    Collect(pc, tail, v);
    PopVec();
    PopVec();
    PopVec();

    if (Debug >= 2)
      fprintf(LogFile, "# tail: [a%d,a%d] = [a%d,[a%d,a%d]] = ", j, i, j, g, h);
  } else if (pc.Generator[i].t == DPOW) { /* ai=N*g */
    gen g = pc.Generator[i].g;
    sparsecvec v = FreshVec();
    Prod(v, pc.Exponent[g], pc.Product[j][g]);
    Collect(pc, tail, v);
    PopVec();

    if (Debug >= 2) {
      fprintf(LogFile, "# tail: [a%d,a%d] = ", j, i);
      coeff_out_str(LogFile, pc.Exponent[g]);
      fprintf(LogFile, "*[a%d,a%d] = ", j, g);
    }
  } else { /* aj = N*g */
    gen g = pc.Generator[j].g;
    sparsecvec v = FreshVec();
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

  unsigned len = 0;
  for (auto kc : pc.Product[j][i]) {
    if (kc.first != tail[len].first || coeff_cmp(kc.second,tail[len].second))
      return false;
    len++;
  }

  if (!tail.issize(len)) {
    pc.Product[j][i].resize(len, tail.size());
    pc.Product[j][i].window(len).copy(tail.window(len));
  }

  PopVec(); /* tail */
  return true;
}

void ComputeTails(const pcpresentation &pc) {
  for (unsigned i = 1; i <= pc.NrPcGens; i++) {
    for (unsigned j = i + 1; j <= pc.NrPcGens; j++) {
      unsigned totalweight = pc.Generator[i].w+pc.Generator[j].w;
      if (totalweight > pc.Class || (pc.Graded && totalweight != pc.Class))
	continue;
      
      if (!AdjustTail(pc, j, i))
	abortprintf(5, "Adjustment to tail of [a%d,a%d] doesn't lie in centre", j, i);
    }
  }
  
  TimeStamp("Tails()");
}
