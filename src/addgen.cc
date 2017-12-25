/******************************************************************************
**
**                 Nilpotent Quotient for Lie Rings
** addgen.c                                                     Csaba Schneider
**                                                           schcs@math.klte.hu
*/

#include "lienq.h"

static void AddSingleGenerator(gpvec &v, gen newgen, deftype def) {
  unsigned l = Length(v);
  v = ResizeVec(v, l, l + 1);
  v[l].g = newgen;
  coeff_set_si(v[l].c, 1);
  v[l+1].g = EOW;
  Definition[newgen] = def;
}

static void ExtendPower(void) {
  /*
  **  Extend the arrays of the generators to the necessary size.
  **  Let's define the newly introduced generators to be central i.e.
  **  All of their product relations will be trivial and also they
  **  have coefficients 0.
  */

  Exponent = (coeff *) realloc(Exponent, (NrTotalGens + 1) * sizeof(coeff));
  if (Exponent == NULL)
    abortprintf(2, "ExtendPower: realloc(Exponent) failed");

  for (unsigned i = NrPcGens + 1; i <= NrTotalGens; i++)
    coeff_init_set_si(Exponent[i], 0);

  Annihilator = (coeff *) realloc(Annihilator, (NrTotalGens + 1) * sizeof(coeff));
  if (Annihilator == NULL)
    abortprintf(2, "ExtendPower: realloc(Annihilator) failed");

  for (unsigned i = NrPcGens + 1; i <= NrTotalGens; i++)
    coeff_init_set_si(Annihilator[i], 0);

  Power = (gpvec *) realloc(Power, (NrTotalGens + 1) * sizeof(gpvec));
  if (Power == NULL)
    abortprintf(2, "ExtendPower: realloc(Power) failed");

  /* The Product arrays will be modified later. */
}

/*
**  The first step is to extend the epimorphism to the next factor.
**  In order to do that we define new generators for the images
**  of the generators of the finite presentation which are not definitions.
*/
void AddGen(presentation &Pres) {
  /*
  **  We want to know in advance the number of the newly introduced generators.
  **  And also don't hesitate to refer this number as 'NrCenGens'.
  */
  NrCenGens = Pres.NrGens + (LastGen[1] * (LastGen[1] - 1)) / 2 +
    LastGen[1] * (NrPcGens - LastGen[1]) - NrPcGens;
  
  for (unsigned i = 1; i <= NrPcGens; i++)
    if (coeff_nz_p(Exponent[i]))
      NrCenGens++;

  /*
  **  In this step we sign the epimorphic images which are definitions.
  **  This is  necessary because we need only to modify the images which
  **  don't define generators.
  */
  bool *IsDefIm = new bool[Pres.NrGens + 1];
  for (unsigned i = 1; i <= Pres.NrGens; i++)
    IsDefIm[i] = false;

  for (unsigned i = 1; i <= NrPcGens; i++)
    if (Definition[i].h == 0) {
      if (0 < (int)Definition[i].g) /* a generator is defined as image of
					presentation generator */
	IsDefIm[Definition[i].g] = true;
      else
	NrCenGens++;
    }

  NrTotalGens += NrCenGens;
    
  /*
  **  We have to sign the defining product relators as well in order to
  **  not get them wrong introducing new generators.
  */
  bool **IsDefRel = new bool *[NrPcGens + 1];
  for (unsigned i = 1; i <= NrPcGens; i++) {
    IsDefRel[i] = new bool[LastGen[1] + 1];
    for (unsigned j = 1; j <= LastGen[1]; j++)
      IsDefRel[i][j] = false;

    if (Definition[i].h != (gen) 0 && Definition[i].h <= LastGen[1])
      IsDefRel[Definition[i].g][Definition[i].h] = true;
  }

  /* Allocate space for the Definition. */
  Definition = (deftype *) realloc(Definition, (NrTotalGens + 1) * sizeof(deftype));
  if (Definition == NULL)
    abortprintf(2, "AddGen: realloc(Definition) failed");
  
  unsigned shift = NrPcGens; /* points to the place of the new/pseudo generator. */

  /* Let's modify the epimorphic images. */
  for (unsigned i = 1; i <= Pres.NrGens; i++)
    if (!IsDefIm[i]) {
      AddSingleGenerator(Epimorphism[i], ++shift, {.g = i, .h = 0});
      if (Debug >= 2)
	fprintf(OutputFile, "# added tail a%d to epimorphic image of %s\n", shift, Pres.Generators[i]);
    }
  
  /*  Could you guess what to do now? Right! Modify the power relations.
   We mark them with a negative h in the Definition field, just to
   check that they DO get eliminated */
  for (unsigned i = 1; i <= NrPcGens; i++)
    if (coeff_nz_p(Exponent[i])) {
	AddSingleGenerator(Power[i], ++shift, {.g = -i, .h = 0});
	if (Debug >= 2)
	  fprintf(OutputFile, "# added tail a%d to torsion generator a%d\n", shift, i);
    }
	
  
  /*  Don't wait more to do our main task!!! */
  for (unsigned i = 1; i <= NrPcGens; i++)
    for (unsigned j = 1; j < i && j <= LastGen[1]; j++)
      if (!IsDefRel[i][j]) {
	AddSingleGenerator(Product[i][j], ++shift, {.g = i, .h = j});
	if (Debug >= 2)
	  fprintf(OutputFile, "# added tail a%d to non-defining commutator [a%d, a%d]\n", shift, i, j);
      }

  if (shift != NrTotalGens)
    abortprintf(5, "AddGen: shift (=%d) != NrTotalGens (=%d)", shift, NrTotalGens);
  
  delete[] IsDefIm;

  for (unsigned i = 1; i <= NrPcGens; i++)
    delete[] IsDefRel[i];
  delete[] IsDefRel;

  ExtendPower();
  
  TimeStamp("AddGen()");
}

void GradedAddGen(void) {
  /*
  **  We want to know in advance the number of the newly introduced generators.
  **  And also don't hazitate to refer this number as 'NrCenGens'.
  */
  if (Class == 2)
    NrCenGens = (LastGen[1] * (LastGen[1] - 1)) / 2;
  else
    NrCenGens = (LastGen[Class-1]-LastGen[Class-2]) * LastGen[1];

  NrTotalGens += NrCenGens;
  
  /* Allocate space for the Definition. */
  Definition = (deftype *) realloc(Definition, (NrTotalGens + 1) * sizeof(deftype));
  if (Definition == NULL)
    abortprintf(2, "GradedAddGen: realloc(Definition) failed");
  
  unsigned shift = NrPcGens; /* points to the place of the new/pseudo generator. */

  for (unsigned i = LastGen[Class-2] + 1; i <= NrPcGens; i++)
    for (unsigned j = 1; j < i && j <= LastGen[1]; j++) {
      AddSingleGenerator(Product[i][j], ++shift, {.g = i, .h = j});
      if (Debug >= 2)
	fprintf(OutputFile, "# added tail a%d to non-defining commutator [a%d, a%d]\n", shift, i, j);
    }
  if (shift != NrTotalGens)
    abortprintf(5, "GradedAddGen: shift (=%d) != NrTotalGens (=%d)", shift, NrTotalGens);

  ExtendPower();

  TimeStamp("GradedAddGen()");
}
