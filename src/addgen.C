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
  Definitions[newgen] = def;
}

static void ExtendCoefficientsAndPower(void) {
  /*
  **  Extend the arrays of the generators to the necessary size.
  **  Let's define the newly introduced generators to be central i.e.
  **  All of their product relations will be trivial and also they
  **  have coefficients 0.
  */

  Coefficients = (coeff *) realloc(Coefficients, (NrTotalGens + 1) * sizeof(coeff));
  if (Coefficients == NULL)
    abortprintf(2, "ExtendCoefficientsAndPower: realloc(Coefficients) failed");

  for (unsigned i = NrPcGens + 1; i <= NrTotalGens; i++)
    coeff_init_set_si(Coefficients[i], 0);

  Power = (gpvec *) realloc(Power, (NrTotalGens + 1) * sizeof(gpvec));
  if (Power == NULL)
    abortprintf(2, "ExtendCoefficientsAndPower: realloc(Power) failed");

  /* The Product arrays will be modify later. */

  if (Debug >= 2) {
    fprintf(OutputFile, "# The newly introduced generators at level %d:\n", Class);
    for (unsigned i = 1; i <= NrCenGens; i++)
      if (Definitions[NrPcGens + i].g)
	fprintf(OutputFile, "# a%d is defined on [ a%d, a%d ]...\n", NrPcGens + i,
	       Definitions[NrPcGens + i].g, Definitions[NrPcGens + i].h);
      else
	fprintf(OutputFile, "# a%d is defined on a power or redundant generator a%d...\n", NrPcGens + i, Definitions[NrPcGens + i].h);
  }
}

/*
**  The first step is to extend the epimorphism to the next factor.
**  In order to do that we define new generators for the images
**  of the generators of the finite presentation which are not definitions.
*/
void AddGen(void) {
  /*
  **  We want to know in advance the number of the newly introduced generators.
  **  And also don't hesitate to refer this number as 'NrCenGens'.
  */
  NrCenGens = Pres.NrGens + (Dimensions[1] * (Dimensions[1] - 1)) / 2 +
    Dimensions[1] * (NrPcGens - Dimensions[1]) - NrPcGens;
  
  for (unsigned i = 1; i <= NrPcGens; i++)
    if (coeff_nz(Coefficients[i]))
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
    if (Definitions[i].h == 0) {
      if (0 < (int)Definitions[i].g) /* a generator is defined as image of
					presentation generator */
	IsDefIm[Definitions[i].g] = true;
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
    IsDefRel[i] = new bool[Dimensions[1] + 1];
    for (unsigned j = 1; j <= Dimensions[1]; j++)
      IsDefRel[i][j] = false;

    if (Definitions[i].h != (gen) 0 && Definitions[i].h <= Dimensions[1])
      IsDefRel[Definitions[i].g][Definitions[i].h] = true;
  }

  /* Allocate space for the Definitions. */
  Definitions = (deftype *) realloc(Definitions, (NrTotalGens + 1) * sizeof(deftype));
  if (Definitions == NULL)
    abortprintf(2, "AddGen: realloc(Definitions) failed");
  
  unsigned shift = NrPcGens; /* points to the place of the new/pseudo generator. */

  /* Let's modify the epimorphic images. */
  for (unsigned i = 1; i <= Pres.NrGens; i++)
    if (!IsDefIm[i])
      AddSingleGenerator(Epimorphism[i], ++shift, {.g = i, .h = 0});

  /*  Could you guess what to do now? Right! Modify the power relations.
   We mark them with a negative h in the Definitions field, just to
   check that they DO get eliminated */
  for (unsigned i = 1; i <= NrPcGens; i++)
    if (coeff_nz(Coefficients[i]))
      {
	fprintf(stderr,"%p power before, len %d\n",Power[i]->c, Length(Power[i]));
	AddSingleGenerator(Power[i], ++shift, {.g = -i, .h = 0});
	fprintf(stderr,"%p power after, len %d\n",Power[i]->c, Length(Power[i]));}
  
  /*  Don't wait more to do our main task!!! */
  for (unsigned i = 1; i <= NrPcGens; i++)
    for (unsigned j = 1; j < i && j <= Dimensions[1]; j++)
      if (!IsDefRel[i][j])
	AddSingleGenerator(Product[i][j], ++shift, {.g = i, .h = j});

  if (shift != NrTotalGens)
    abortprintf(5, "AddGen: shift (=%d) != NrTotalGens (=%d)", shift, NrTotalGens);
  
  delete[] IsDefIm;

  for (unsigned i = 1; i <= NrPcGens; i++)
    delete[] IsDefRel[i];
  delete[] IsDefRel;

  ExtendCoefficientsAndPower();
  
  TimeStamp("AddGen()");
}

void GradedAddGen(void) {
  unsigned lwbd;

  /*
  **  We want t know in advance the number of the newly introduced generators.
  **  And also don't hazitate to refer this number as 'NrCenGens'.
  */
  if (Class == 2)
    NrCenGens = (Dimensions[1] * (Dimensions[1] - 1)) / 2;
  else
    NrCenGens = Dimensions[Class - 1] * Dimensions[1];

  NrTotalGens += NrCenGens;
  
  /* Allocate space for the Definitions. */
  Definitions = (deftype *) realloc(Definitions, (NrTotalGens + 1) * sizeof(deftype));
  if (Definitions == NULL)
    abortprintf(2, "GradedAddGen: realloc(Definitions) failed");
  
  unsigned shift = NrPcGens; /* points to the place of the new/pseudo generator. */

  SUM(Dimensions, Class - 2, lwbd);
  for (unsigned i = lwbd + 1; i <= NrPcGens; i++)
    for (unsigned j = 1; j < i && j <= Dimensions[1]; j++)
      AddSingleGenerator(Product[i][j], ++shift, {.g = i, .h = j});

  if (shift != NrTotalGens)
    abortprintf(5, "GradedAddGen: shift (=%d) != NrTotalGens (=%d)", shift, NrTotalGens);

  ExtendCoefficientsAndPower();

  TimeStamp("GradedAddGen()");
}
