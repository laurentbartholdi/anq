/******************************************************************************
**
**                 Nilpotent Quotient for Lie Rings
** operations.c                                                 Csaba Schneider
**                                                           schcs@math.klte.hu
*/

#include "lienq.h"

/*
** The purpose of this couple of functions is to handle the Lie-algebra
** operations in the PC-presentation. There are 3 main operations i.e.
** a summation:        with respect to this the elements form an Abelian-group;
** a Lie product:      equipped with the usual Jacoby, anti-commutativity, and
**                     distributivity. It is stored in the Power[][] matrix.
** an integer-product: A modul-operation of course. Makes no problem(?).
*/

/*
**  The following function writes a coeffvec in normal form i.e. cancels the
**  coefficients that are not allowed becausee of the power relations. The
**  result remains in <ev>.
*/

void CollectCoeffVec(coeffvec ev) {
  for (unsigned i = 1; i <= NrPcGens + NrCenGens; i++) {
    coeff mp = ev[i].reduce(Coefficients[i]);
    if (mp.notzero()) {
      ev[i] -= mp * Coefficients[i];
      for (gpvec p = Power[i]; p->g != EOW; p++)
        ev[p->g] += mp * p->c;
    }
  }
}

void Collect(gpvec v0, gpvec gv) {
  coeffvec cv;

  cv = GpVecToCoeffVec(gv);
  CollectCoeffVec(cv);
  CoeffVecToGpVec(v0,cv);
  free(cv);
}

#if 1
gpvec Collect(gpvec gv) {
  coeffvec cv;
  gpvec gv1;

  cv = GpVecToCoeffVec(gv);
  CollectCoeffVec(cv);
  gv1 = CoeffVecToGpVec(cv);

  free(cv);
  return gv1;
}
#else
gpvec Collect(gpvec gv) {
  gpvec result = malloc(lots...);
  struct { coeff c; gpvec p; } *queue = malloc(lots...);
  queue[0] = { 1, gv };
  int qlen = 1, gen  = 0;
  while (qlen > 0) {
    find minimum of all gens in queue; when one queue is exhausted, pop;
    sum all corresponding coefficients;
    if non-zero, reduce; and if non-trivial reduction, add power to queue;
    if non-zero, put in result;
  }
  return result;
}
#endif

/* vec0 = vec1 + vec2 */
void Sum(gpvec vec0, gpvec vec1, gpvec vec2) {
  for (;;) {
    if (vec1->g == EOW) {
      while (vec2->g != EOW) *vec0++ = *vec2++;
      goto done;
    }
    if (vec2->g == EOW) {
      while (vec1->g != EOW) *vec0++ = *vec1++;
      goto done;
    }
    if (vec1->g < vec2->g)
      *vec0++ = *vec1++;
    else if (vec1->g > vec2->g)
      *vec0++ = *vec2++;
    else {
      coeff c = vec1->c + vec2->c;
      if (c.notzero())
	vec0->c = c, vec0->g = vec1->g, vec0++;
      vec1++;
      vec2++;
    }
  }
 done:
  vec0->g = EOW;
}

/* vec0 = vec1 + x*vec2 */
void Sum(gpvec vec0, gpvec vec1, coeff x, gpvec vec2) {
  if (!x.notzero()) {
      while (vec1->g != EOW) *vec0++ = *vec1++;
      goto done;    
  }
  
  for (;;) {
    if (vec1->g == EOW) {
      while (vec2->g != EOW) {
	vec0->c = x*vec2->c, vec0->g = vec2->g;
	vec0++;
	vec2++;
      }
      goto done;
    }
    if (vec2->g == EOW) {
      while (vec1->g != EOW) *vec0++ = *vec1++;
      goto done;
    }
    if (vec1->g < vec2->g)
      *vec0++ = *vec1++;
    else if (vec1->g > vec2->g) {
      vec0->c = x*vec2->c, vec0->g = vec2->g;
      vec0++;
      vec2++;
    } else {
      coeff c = vec1->c + x*vec2->c;
      if (c.notzero())
	vec0->c = c, vec0->g = vec1->g, vec0++;
      vec1++;
      vec2++;
    }
  }
 done:
  vec0->g = EOW;
}

/* puts n * vec into vec */
void ModProd(coeff n, gpvec vec) {
  for (; vec->g != EOW; vec++)
    vec->c *= n;
}

/* puts -vec into vec */
void ModNeg(gpvec vec) {
  for(; vec->g != EOW; vec++)
    vec->c = -vec->c;
}

/* vec0 = [ vec1, vec2 ] */
void Prod(gpvec vec0, gpvec vec1, gpvec vec2) {
  gpvec temp[2];
  bool parity = 0;
  temp[0] = NewGpVec(NrCenGens + NrPcGens);
  temp[1] = NewGpVec(NrCenGens + NrPcGens);
  temp[0][0].g = EOW;
  
  for (gpvec p1 = vec1; p1->g != EOW; p1++)
    for (gpvec p2 = vec2; p2->g != EOW; p2++)
      if (p1->g <= NrPcGens && p2->g <= NrPcGens && Weight[p1->g] + Weight[p2->g] <= Class) {
        if (p1->g > p2->g)
	  Sum(temp[!parity], temp[parity], p1->c*p2->c, Product[p1->g][p2->g]), parity ^= 1;
	else if (p2->g > p1->g)
	  Sum(temp[!parity], temp[parity], -p1->c*p2->c, Product[p2->g][p1->g]), parity ^= 1;
      }
  CpVec(vec0, temp[parity]);
  free(temp[0]);
  free(temp[1]);
}
