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

static void Tail_ab(gpvec v, gen a, gen b) {
  if (Weight[a] + Weight[b] > Class)
    return;

  gen g = Definitions[b].g, h = Definitions[b].h;
  
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
    fprintf(OutputFile, "# tail: [ %d, %d ] = ", a, b);
    PrintVec(v);
    fprintf(OutputFile, "\n");
  }
}

void Tails(void) {
  for (unsigned i = Dimensions[1] + 1; i <= NrPcGens; i++)
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
  unsigned lwbd, lwbd1, upbd, upbd1;

  for (unsigned k = 2; k <= Class / 2; k++) {
    SUM(Dimensions, k - 1, lwbd);
    SUM(Dimensions, k, upbd);
    for (unsigned i = lwbd + 1; i <= upbd; i++) {
      SUM(Dimensions, Class - k - 1, lwbd1);
      SUM(Dimensions, Class - k, upbd1);
      for (unsigned j = MAX(i + 1, lwbd1 + 1); j <= upbd1; j++) {
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
    }
  }

  TimeStamp("GradedTails()");
}
