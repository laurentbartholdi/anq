/******************************************************************************
**
**                 Nilpotent Quotient for Lie Rings
** epim.c                                                       Csaba Schneider
**                                                           schcs@math.klte.hu
*/

#include "lienq.h"

/*
** The epimorphism maps from the Lie-algebra given by finite presentation to
** the nilpotent factor-algebra computed by the LieNQ algorithm.
*/

/*
** We initialize the epimorphism from the finite presentation to the first
** (abelian) factor. It is rather trivial at the beginning, actually a
** one-to-one map between the two generator set.
*/
void InitEpim(void) {
  Epimorphism = (gpvec *) malloc((Pres.NrGens + 1) * sizeof(gpvec));
  for (unsigned i = 1; i <= Pres.NrGens; i++) {
    Epimorphism[i] = NewVec(1);
    Epimorphism[i][0].g = i;
    coeff_init_set_si(Epimorphism[i][0].c, 1);
    Epimorphism[i][1].g = EOW;
    Definitions[i] = {.g = i, .h = 0};
  }
}

void FreeEpim(void) {
  for (unsigned i = 1; i <= Pres.NrGens; i++)
    FreeVec(Epimorphism[i]);
  free(Epimorphism);
}
