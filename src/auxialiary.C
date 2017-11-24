/******************************************************************************
**
**               Nilpotent Quotient for Lie Algebras
** auxialiary.c                                                 Csaba Schneider
**                                                           schcs@math.klte.hu
*/

#include "lienq.h"

gpvec NewGpVec(unsigned size) {
  gpvec v = (gpvec) malloc ((size+1)*sizeof v[0]);
  if (v == NULL) {
    perror("NewGpVec: malloc failed");
    exit(2);
  }
  return v;
}

coeffvec NewCoeffVec(void) {
  coeffvec v = (coeffvec) calloc((NrPcGens + NrCenGens + 1), sizeof v[0]);
  if (v == NULL) {
    perror("NewCoeffVec: malloc failed");
    exit(2);
  }
  return v;
}

void CpVec(gpvec vec1, gpvec vec2) {
  unsigned i = 0;

  while (vec2[i].g != EOW) {
    vec1[i].g = vec2[i].g;
    vec1[i].c = vec2[i].c;
    i++;
  }
  vec1[i].g = EOW;
}

/* The same as the previous one but frees vec2 */
void CpVecFree(gpvec vec1, gpvec vec2)

{
  unsigned i = 0;

  while (vec2[i].g != EOW) {
    vec1[i].g = vec2[i].g;
    vec1[i].c = vec2[i].c;
    i++;
  }
  vec1[i].g = EOW;
  free(vec2);
}

/*
**  GenToCoeffVec( n )  returns the coefficient vector corresponding
**  the generator <n> i.e. a vector which has 1 in the n-th entry
**  and zero otherwise.
*/

gpvec GenToGpVec(gen n) {
  gpvec gv = NewGpVec(1);
  gv[0].g = n;
  gv[0].c = 1;
  gv[1].g = EOW;

  return gv;
}

/*   The following function stands for computing the Length for an
**   arbitrary genpower vector.
*/

unsigned Length(gpvec vec) {
  unsigned l = 0;

  while (vec[l].g != EOW) l++;
  
  return l;
}

/* Compute the real length (number of nonzero elements in a coeffvec. */

unsigned RealLength(coeffvec cv) {
  unsigned l = 0;

  for (unsigned i = 1; i <= NrPcGens + NrCenGens; i++)
    if (cv[i].notzero())
      l++;

  return l;
}

/*  We might need to convert the two form of the Lie ring elements to each
**  other (and indeed we do it sometimes), so the following functions are
**  useful.
*/

void CoeffVecToGpVec(gpvec gv, coeffvec cv) {
  gpvec p = gv;
  
  for (unsigned i = 1; i <= NrPcGens + NrCenGens; i++)
    if (cv[i].notzero()) {
      p->g = i;
      p->c = cv[i];
      p++;
    }
  p->g = EOW;
}

gpvec CoeffVecToGpVec(coeffvec cv) {
  gpvec gv = NewGpVec(RealLength(cv));
  CoeffVecToGpVec(gv, cv);
  return gv;
}

coeffvec GpVecToCoeffVec(gpvec gv) {
  coeffvec cv;

  cv = NewCoeffVec();
  for (int i = 0; gv[i].g != EOW; i++)
    cv[gv[i].g] = gv[i].c;

  return cv;
}

/* shrink a gpvec to correct length */
gpvec ShrinkGpVec(gpvec v) {
  unsigned l = Length(v);
  v = (gpvec) realloc (v, (l+1)*sizeof v[0]);
  if (v == NULL) {
    perror("realloc failed");
    exit(2);
  }
  return v;
}
