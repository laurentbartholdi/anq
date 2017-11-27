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
  for (unsigned i = 0; i < size; i++)
    coeff_init(v[i].c);
  
  return v;
}

void FreeGpVec(gpvec v, unsigned size) {
  for (unsigned i = 0; i < size; i++)
    coeff_clear(v[i].c);
  free(v);
}

void FreeGpVec(gpvec v) {
  for (gpvec p = v; p->g != EOW; p++)
    coeff_clear(p->c);
  free(v);
}

coeffvec NewCoeffVec(void) {
  coeffvec v = (coeffvec) calloc((NrTotalGens + 1), sizeof v[0]);
  if (v == NULL) {
    perror("NewCoeffVec: malloc failed");
    exit(2);
  }
  for (unsigned i = 1; i <= NrTotalGens; i++)
    coeff_init(v[i]);
  
  return v;
}

void ZeroCoeffVec(coeffvec v) {
  for (unsigned i = 1; i <= NrTotalGens; i++)
    coeff_set_si(v[i], 0);
}

void FreeCoeffVec(coeffvec v) {
  for (unsigned i = 1; i <= NrTotalGens; i++)
    coeff_clear(v[i]);
  free(v);
}

void CpVec(gpvec vec1, constgpvec vec2) {
  unsigned i = 0;

  while (vec2[i].g != EOW) {
    vec1[i].g = vec2[i].g;
    coeff_set(vec1[i].c, vec2[i].c);
    i++;
  }
  vec1[i].g = EOW;
}

/*
**  GenToCoeffVec( n )  returns the coefficient vector corresponding
**  the generator <n> i.e. a vector which has 1 in the n-th entry
**  and zero otherwise.
*/

gpvec GenToGpVec(gen n) {
  gpvec gv = NewGpVec(1);
  gv[0].g = n;
  coeff_init_set_si(gv[0].c, 1);
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

  for (unsigned i = 1; i <= NrTotalGens; i++)
    if (coeff_nz(cv[i]))
      l++;

  return l;
}

/*  We might need to convert the two form of the Lie ring elements to each
**  other (and indeed we do it sometimes), so the following functions are
**  useful.
*/

void CoeffVecToGpVec(gpvec gv, coeffvec cv) {
  gpvec p = gv;
  
  for (unsigned i = 1; i <= NrTotalGens; i++)
    if (coeff_nz(cv[i])) {
      p->g = i;
      coeff_set(p->c, cv[i]);
      p++;
    }
  p->g = EOW;
}

gpvec CoeffVecToGpVec(coeffvec cv) {
  gpvec gv = NewGpVec(RealLength(cv));
  CoeffVecToGpVec(gv, cv);
  return gv;
}

coeffvec GpVecToCoeffVec(constgpvec gv) {
  coeffvec cv;

  cv = NewCoeffVec();
  for (constgpvec p = gv; p->g != EOW; p++)
    coeff_set(cv[p->g], p->c);

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
