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

static void Tail_ab(gpvec v, gen a, gen b) {
  if (Weight[a] + Weight[b] > Class)
    return;

  gen g = Definition[b].g, h = Definition[b].h;
  
  gpvec agh = FreshVec();
  TripleProduct(agh, a, g, h);
  gpvec ahg = FreshVec();
  TripleProduct(ahg, a, h, g);
  gpvec tail = FreshVec();
  Diff(tail, agh, ahg);
  Collect(v, tail);
  PopVec();
  PopVec();
  PopVec();

  if (Debug >= 2) {
    fprintf(OutputFile, "# tail: [a%d,a%d] = ", a, b);
    PrintVec(v);
    fprintf(OutputFile, "\n");
  }
}

void Tails(void) {
  for (unsigned i = LastGen[1] + 1; i <= NrPcGens; i++)
    for (unsigned j = i + 1; j <= NrPcGens; j++) {
      gpvec tail = FreshVec();
      Tail_ab(tail, j, i);
      unsigned k;
      for (k = 0; Product[j][i][k].g != EOW; k++)
	if (Product[j][i][k].g != tail[k].g || coeff_cmp(Product[j][i][k].c,tail[k].c))
	  abortprintf(5, "Tail [a,g,h]-[a,h,g]-[a,[g,h]] doesn't lie in centre for a=a%d,[g,h]=a%d", j, i);

      if (tail[k].g != EOW) {
	Product[j][i] = ResizeVec(Product[j][i], k, Length(tail));
	Copy(Product[j][i]+k, tail+k);
      }
      PopVec();
    }

  TimeStamp("Tails()");
}

void GradedTails(void) {
  for (unsigned k = 2; k <= Class / 2; k++)
    for (unsigned i = LastGen[k-1] + 1; i <= LastGen[k]; i++)
      for (unsigned j = std::max(i + 1, LastGen[Class-k-1] + 1); j <= LastGen[Class-k]; j++) {
	gpvec tail = FreshVec();
	Tail_ab(tail, j, i);
	unsigned k;
	for (k = 0; Product[j][i][k].g != EOW; k++)
	  if (Product[j][i][k].g != tail[k].g || coeff_cmp(Product[j][i][k].c,tail[k].c))
	  abortprintf(5, "Tail [a,g,h]-[a,h,g]-[a,[g,h]] doesn't lie in centre for a=a%d,[g,h]=a%d", j, i);
	
	if (tail[k].g != EOW) {
	  Product[j][i] = ResizeVec(Product[j][i], k, Length(tail));
	  Copy(Product[j][i]+k, tail+k);
	}
	PopVec();
      }

  TimeStamp("GradedTails()");
}
