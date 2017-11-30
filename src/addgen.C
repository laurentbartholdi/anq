/******************************************************************************
**
**                 Nilpotent Quotient for Lie Rings
** addgen.c                                                     Csaba Schneider
**                                                           schcs@math.klte.hu
*/

#include "lienq.h"

/*
**  The first step is to extend the epimorphism to the next factor.
**  In order to do that we define new generators for the images
**  of the generators of the finite presentation which are not definitions.
*/

void AddGen(void) {
  bool *IsDefIm;
  int shift, sign, lwbd;
  bool **IsDefRel;

  /*
  **  We want t know in advance the number of the newly introduced generators.
  **  And also don't hazitate to refer this number as 'NrCenGens'.
  */
  if (Graded)
    if (Class == 2)
      NrCenGens = (Dimensions[1] * (Dimensions[1] - 1)) / 2;
    else
      NrCenGens = Dimensions[Class - 1] * Dimensions[1];
  else
    NrCenGens = Pres.NrGens + (Dimensions[1] * (Dimensions[1] - 1)) / 2 +
                Dimensions[1] * (NrPcGens - Dimensions[1]) - NrPcGens;

  NrTotalGens += NrCenGens;
  
  if (!Graded)
    for (unsigned i = 1; i <= NrPcGens; i++)
      if (coeff_nz(Coefficients[i]))
        NrCenGens++, NrTotalGens++;

  /*
  **  In this step we sign the epimorphic images which are definitions.
  **  This is  necessery because we need only to modify the images which
  **  don't define generators. In the graded  case the we don't need to
  **  do it.
  */
  if (!Graded) {
    IsDefIm = new bool[Pres.NrGens + 1];
    for (unsigned i = 1; i <= Pres.NrGens; i++)
      IsDefIm[i] = false;

    for (unsigned i = 1; i <= NrPcGens; i++)
      if (Definitions[i].h == 0)
        IsDefIm[Definitions[i].g] = true;
  }

  /*
  **  We have to sign the defining product relators as well in order to
  **  not get them wrong introducing new generators.
  */
  IsDefRel = new bool *[NrPcGens + 1];
  for (unsigned i = 1; i <= NrPcGens; i++) {
    IsDefRel[i] = new bool[Dimensions[1] + 1];
    for (unsigned j = 1; j <= Dimensions[1]; j++)
      IsDefRel[i][j] = false;

    if (Definitions[i].h != (gen) 0 && Definitions[i].h <= Dimensions[1])
      IsDefRel[Definitions[i].g][Definitions[i].h] = true;
  }

  /* Allocate space for the Definitions. */
  Definitions = (deftype *) realloc(Definitions, (NrTotalGens + 1) * sizeof(deftype));
  if (Definitions == NULL) {
    perror("AddGen: realloc(Definitions) failed");
    exit(2);
  }
  
  shift = NrPcGens + 1; /* points to the place of the new/pseudo generator. */
  if (!Graded) {
    /* Let's modify the epimorphic images. */
    for (unsigned i = 1; i <= Pres.NrGens; i++)
      if (!IsDefIm[i]) {
        unsigned l = Length(Epimorphism[i]);
        Epimorphism[i] = ResizeVec(Epimorphism[i], l + 1);
        Epimorphism[i][l].g = shift;
        coeff_init_set_si(Epimorphism[i][l].c, 1);
        Epimorphism[i][l+1].g = EOW;
	Definitions[shift].g = 0;
	Definitions[shift++].h = -i;
      }
  }

  if (!Graded)
    /*  Could you guess what to do now? Right! Modify the power relations.
        But of course only in the not graded case.*/
    for (unsigned i = 1; i <= NrPcGens; i++)
      if (coeff_nz(Coefficients[i])) {
        unsigned l = Length(Power[i]);
        Power[i] = ResizeVec(Power[i], l + 1);
        Power[i][l].g = shift;
        coeff_init_set_si(Power[i][l].c, 1);
        Power[i][l+1].g = EOW;
	Definitions[shift].g = 0;
	Definitions[shift++].h = i;
      }

  /*  Don't wait more to do our main task!!! */
  if (!Graded) {
    for (unsigned i = 1; i <= NrPcGens; i++)
      for (unsigned j = 1; j <= MIN(i - 1, Dimensions[1]); j++)
        if (!IsDefRel[i][j]) {
          unsigned l = Length(Product[i][j]);
          Product[i][j] = ResizeVec(Product[i][j], l + 1);
          Product[i][j][l].g = shift;
          coeff_init_set_si(Product[i][j][l].c, 1);
          Product[i][j][l+1].g = EOW;
          Definitions[shift].g = i;
          Definitions[shift++].h = j;
        }
  } else { /* The graded case. */
    SUM(Dimensions, Class - 2, lwbd);
    for (unsigned i = lwbd + 1; i <= NrPcGens; i++)
      for (unsigned j = 1; j <= MIN(i - 1, Dimensions[1]); j++) {
        unsigned l = Length(Product[i][j]);
        Product[i][j] = ResizeVec(Product[i][j], l + 1);
        Product[i][j][l].g = shift;
        coeff_init_set_si(Product[i][j][l].c, 1);
        Product[i][j][l+1].g = EOW;
        Definitions[shift].g = i;
        Definitions[shift++].h = j;
        sign = !sign;
      }
  }
  /*
  **  Extend the arrays of the generators to the necessary size.
  **  Let's define the newly introduced generators to be central i.e.
  **  All of their product relations will be trivial and also they
  **  have coefficients 0.
  */

  Coefficients = (coeff *) realloc(Coefficients, (NrTotalGens + 1) * sizeof(coeff));
  if (Coefficients == NULL) {
    perror("AddGen: realloc(Coefficients) failed");
    exit(2);
  }
  for (unsigned i = NrPcGens + 1; i <= NrTotalGens; i++)
    coeff_init_set_si(Coefficients[i], 0);

  Power = (gpvec *) realloc(Power, (NrTotalGens + 1) * sizeof(gpvec));
  if (Power == NULL) {
    perror("AddGen: realloc(Power) failed");
    exit(2);
  }

  /* The Product arrays will be modify later. */

  /* free the local structures. */
  if (!Graded)
    delete IsDefIm;

  for (unsigned i = 1; i <= NrPcGens; i++)
    delete IsDefRel[i];
  delete IsDefRel;

  if (Debug)
    fprintf(OutputFile, "# AddGen() finished\n");

  if (Debug) {
    fprintf(OutputFile, "# The newly introduced generators at level %d:\n", Class);
    for (unsigned i = 1; i <= NrCenGens; i++)
      if (Definitions[NrPcGens + i].g)
	fprintf(OutputFile, "# a%d is defined on [ a%d, a%d ]...\n", NrPcGens + i,
	       Definitions[NrPcGens + i].g, Definitions[NrPcGens + i].h);
      else
	fprintf(OutputFile, "# a%d is defined on a power or redundant generator a%d...\n", NrPcGens + i, Definitions[NrPcGens + i].h);
  }
}
