/******************************************************************************
**
**                 Nilpotent Quotient for Lie Rings
** presentation.c                                               Csaba Schneider
**                                                           schcs@math.klte.hu
*/

#include "lienq.h"
#include <time.h> // for clock

gpvec **Product,  *Power, *Epimorphism;
coeff *Coefficients;

unsigned *Weight, *Dimensions;

deftype *Definitions;

unsigned NrCenGens, NrPcGens, NrTotalGens;

void InitPcPres(void) {
  /*
  ** We initialize the power-relations to be trivial.
  */
  Coefficients = (coeff *) malloc((Pres.NrGens + 1) * sizeof(coeff));
  if (Coefficients == NULL)
    abortprintf(2, "InitPcPres: malloc(Coefficients) failed");

  for (unsigned i = 1; i <= Pres.NrGens; i++)
    coeff_init(Coefficients[i]);
  
  /*
  ** Suppose the power-relations to be in collected word, so it is enough
  ** to restore their coefficient vectors.
  */
  Power = (gpvec *) malloc((Pres.NrGens + 1) * sizeof(gpvec));
  if (Power == NULL)
    abortprintf(2, "InitPcPres: malloc(Power) failed");

  /* The product relations are trivial too (yet).*/
  Product = (gpvec **) malloc((Pres.NrGens + 1) * sizeof(gpvec *));
  if (Product == NULL)
    abortprintf(2, "InitPcPres: malloc(Product) failed");

  /* We allocate space for the Definitions[]. */
  Definitions = (deftype *) malloc((Pres.NrGens + 1) * sizeof(deftype));
  if (Definitions == NULL)
    abortprintf(2, "InitPcPres: malloc(Definitions) failed");

  /*
  **  And finally the Dimensions will contain the number of the
  **  generators correspond to a certain weight.
  */
  Dimensions = (unsigned *) malloc(1 * sizeof(unsigned));
  if (Dimensions == NULL)
    abortprintf(2, "InitPcPres: malloc(Dimensions) failed");
  Dimensions[0] = 0;

  Weight = (unsigned *) malloc(1 * sizeof(unsigned));
  if (Weight == NULL)
    abortprintf(2, "InitPcPres: malloc(Weight) failed");

  NrCenGens = NrTotalGens = Pres.NrGens;
  NrPcGens = 0;
}

void FreePcPres(void) {
  for (unsigned i = 1; i <= NrTotalGens; i++) {
    if (coeff_nz(Coefficients[i]))
      FreeVec(Power[i]);
    coeff_clear(Coefficients[i]);
    for (unsigned j = 1; j < i; j++)
      FreeVec(Product[i][j]);
    free(Product[i]);
  }
  free(Power);
  free(Coefficients);
  free(Product);
  free(Definitions);
  free(Dimensions);
  free(Weight);
}

/* This is time-critical. It can be optimized in various ways:
   -- g is a central generator, so we can skip the beginning if we ever
      have to call Diff
   -- Matrix is in Hermite normal form -- we could put it in Smith NF, maybe,
      and then the collection would be simpler?
   -- often w will have only 1 or 2 non-trivial entries, in which case the
      operation can be done in-place
*/

void EliminateTrivialGenerators(gpvec &v, int renumber[]) {
  bool copied = false;
  unsigned pos = 0;

  for (; v[pos].g != EOW;) {
    int newg = renumber[v[pos].g];
    if (newg >= 1) {
      v[pos].g = newg;
      pos++;
    } else {
      gpvec rel = Matrix[-newg];
      gpvec temp = FreshVec();
      Diff(temp, v+pos+1, v[pos].c, rel+1);
      if (!copied) { /* we should make sure we have enough space */
	gpvec newv = NewVec(NrTotalGens);
	v[pos].g = EOW; /* cut original p at this position, copy to newv */
	Copy(newv, v);
	v[pos].g = rel->g; /* put it back, so we can free correctly v */
	FreeVec(v);
	v = newv;
      }
      Copy(v+pos, temp);
      PopVec();
      copied = true;
    }
  }
  if (copied)
    v = ResizeVec(v, NrTotalGens, pos);
  ShrinkCollect(v);
}
  
void EvalAllRel(void) {
  gpvec v = FreshVec();
  for (unsigned i = 0; i < Pres.NrRels; i++) {
    gpvec temp = FreshVec();
    EvalRel(temp, Pres.Relators[i]);
    Collect(v, temp);
    PopVec();
    if (Debug >= 2) {
      fprintf(OutputFile, "# relation: ");
      PrintVec(v);
      fprintf(OutputFile, "\n");
    }
    AddRow(v);
  }
  PopVec();
  
  TimeStamp("EvalAllRel()");
}

unsigned ReducedPcPres(void) {
  unsigned trivialgens = 0;

  if (Debug >= 2) {
    fprintf(OutputFile, "# relations matrix:\n");
    for (unsigned i = 0; i < NrRows; i++) {
      fprintf(OutputFile, "# "); PrintVec(Matrix[i]); fprintf(OutputFile, "\n");
    }
  }

  /* renumber[k] = j >= 1 means generator k should be renumbered j.
     renumber[k] = j <= 0 means generator k should be eliminated using row j */
  int *renumber = new int[NrTotalGens + 1];
  
  for (unsigned k = 1, i = 0; k <= NrTotalGens; k++) {
    unsigned newk = renumber[k] = k - trivialgens;
    if (i >= NrRows || k != Matrix[i]->g) /* no relation for k, remains */
      continue;

    if (coeff_cmp_si(Matrix[i]->c, 1)) { /* k is torsion, nontrivial */
      coeff_set(Coefficients[newk], Matrix[i]->c);
      Power[newk] = NewVec(Length(Matrix[i]+1));
      Neg(Power[newk], Matrix[i]+1);
    } else { /* k is trivial, and will be eliminated */
      trivialgens++;
      renumber[k] = -i; /* mark as trivial */
    }
    i++;
  }

  /* Modify the torsions first, in decreasing order, since they're needed
     for Collect */
  for (unsigned j = NrTotalGens; j >= 1; j--)
    if (coeff_nz(Coefficients[j]))
      EliminateTrivialGenerators(Power[j], renumber);
  
  /*  Modify the epimorphisms: */
  for (unsigned j = 1; j <= Pres.NrGens; j++)
    EliminateTrivialGenerators(Epimorphism[j], renumber);
  
  /*  Modify the products: */
  for (unsigned j = 1; j <= NrPcGens; j++)
    for (unsigned l = 1; l < j; l++)
      EliminateTrivialGenerators(Product[j][l], renumber);

  /* Let us alter the Definitions as well. Recall that dead generator cannot
  have definition at all. It is only the right of the living ones. */
  for (unsigned i = NrPcGens + 1; i <= NrTotalGens; i++)
    if (renumber[i] >= 1)
      Definitions[renumber[i]] = Definitions[i];
  
  for (unsigned i = 1; i <= NrTotalGens; i++)
    if (Definitions[i].h == 0 && 0 > (int)Definitions[i].g) {
      fprintf(stderr, "\aDefinition of generator %d is neither image of presentation generator nor commutator,\nbut rather power of generator %d. I'm almost surely screwed up, cross your fingers.\n", i, -Definitions[i].g);
    }
    
  delete[] renumber;

  for (unsigned i = 0; i < trivialgens; i++)
    coeff_clear(Coefficients[NrTotalGens - i]);
  
  TimeStamp("ReducedPcPres()");

  return trivialgens;
}

void ExtendPcPres(void) {
  Dimensions = (unsigned *) realloc(Dimensions, (Class + 1) * sizeof(unsigned));
  if (Definitions == NULL)
    abortprintf(2, "ExtendPcPres: realloc(Definitions) failed");

  Dimensions[Class] = NrCenGens;

  Weight = (unsigned *) realloc(Weight, (NrTotalGens + 1) * sizeof(unsigned));
  if (Weight == NULL)
    abortprintf(2, "ExtendPcPres: realloc(Weight) failed");

  for (unsigned i = NrPcGens + 1; i <= NrTotalGens; i++)
    Weight[i] = Class;

  /*
  ** Because of the anti-symmetry we need only to store the product-relations
  ** of the form [ i, j ] when i>j (sorry...). Hence the form of their 'matrix'
  ** turns into triangle-shaped. The row corresponding to the i-th generotor
  *will
  ** be of length i-1.
  */

  Product = (gpvec **) realloc(Product, (NrTotalGens + 1) * sizeof(gpvec *));
  if (Product == NULL)
    abortprintf(2, "ExtendPcPres: realloc(Product) failed");

  for (unsigned i = NrPcGens + 1; i <= NrTotalGens; i++) {
    Product[i] = (gpvec *) malloc(i * sizeof(gpvec));
    if (Product[i] == NULL)
      abortprintf(2, "ExtendPcPres: realloc(Product[%d]) failed", i);

    for (unsigned j = 1; j < i; j++) {
      Product[i][j] = NewVec(0);
      Product[i][j][0].g = EOW;
    }
  }

  NrPcGens += NrCenGens;
  NrCenGens = 0;
}
