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
  Coefficients = (coeff *) calloc(Pres.NrGens + 1, sizeof(coeff));
  if (Coefficients == NULL) {
    perror("InitPcPres, Coefficients");
    exit(2);
  }

  /*
  ** Suppose the power-relations to be in collected word, so it is enough
  ** to restore their coefficient vectors.
  */
  Power = (gpvec *)malloc((Pres.NrGens + 1) * sizeof(gpvec));

  /* The product relations are trivial too (yet).*/
  Product = (gpvec **)malloc((Pres.NrGens + 1) * sizeof(gpvec *));

  if (Product == NULL) {
    perror("InitPcPres, Product");
    exit(2);
  }

  /* We allocate space for the Definitions[]. */
  Definitions = (deftype *)malloc((Pres.NrGens + 1) * sizeof(deftype));

  /*
  **  And finally the Dimensions will contain the number of the
  **  generators correspond to a certain weight.
  */
  Dimensions = (unsigned *)malloc(1 * sizeof(unsigned));
  Dimensions[0] = 0;

  Weight = (unsigned *)malloc(1 * sizeof(unsigned));

  NrCenGens = NrTotalGens = Pres.NrGens;
  NrPcGens = 0;
}

void FreePcPres(void) {
  for (unsigned i = 1; i <= NrTotalGens; i++)
    if (coeff_nz(Coefficients[i]))
      FreeVec(Power[i]);
  free(Power);
  free(Coefficients);
  for (unsigned i = 1; i <= NrTotalGens; i++) {
    for (unsigned j = 1; j < i; j++)
      FreeVec(Product[i][j]);
    free(Product[i]);
  }
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

void EliminateTrivialGenerators(gpvec &v, int renumber[], gpvec relation[]) {
  bool copied = false;
  gpvec p = v;

  for (; p->g != EOW;) {
    int newg = renumber[p->g];
    if (newg >= 1) {
      p->g = newg;
      p++;
    } else {
      gpvec rel = relation[-newg];
      gpvec temp = FreshVec();
      Diff(temp, p+1, p->c, rel+1);
      if (!copied) { /* we should make sure we have enough space */
	gpvec newv = NewVec(NrTotalGens);
	p->g = EOW; /* cut original p at this position, copy to newv */
	Copy(newv, v);
	p = p-v + newv;
	FreeVec(v);
	v = newv;
      }
      Copy(p, temp);
      PopVec();
      copied = true;
    }
  }

  ShrinkCollect(v);
}
  
void EvalAllRel(void) {
  gpvec v = FreshVec();
  for (unsigned i = 0; i < Pres.NrRels; i++) {
    gpvec temp = FreshVec();
    EvalRel(temp, Pres.Relators[i]);
    Collect(v, temp);
    PopVec();
    if (Debug) {
      fprintf(OutputFile, "# relation: ");
      PrintVec(v);
      fprintf(OutputFile, "\n");
    }
    AddRow(v);
  }
  PopVec();
  
  if (Debug)
    fprintf(OutputFile, "# EvalAllRel() finished\n");
}

void UpdatePcPres(void) {
  unsigned trivialgens = 0;

  gpvec *ExpMat = MatrixToExpVecs();
  if (Debug) {
    for (unsigned i = 0; i < NrRows; i++) {
      PrintVec(ExpMat[i]);
      fprintf(OutputFile, "\n");
    }
  }

  /* renumber[k] = j >= 1 means generator k should be renumbered j.
     renumber[k] = j <= 0 means generator k should be eliminated using row j */
  int *renumber = new int[NrTotalGens + 1];
  
  for (unsigned k = 1, i = 0; k <= NrTotalGens; k++) {
    unsigned newk = renumber[k] = k - trivialgens;
    if (i >= NrRows || k != ExpMat[i]->g) /* no relation for k, remains */
      continue;

    if (coeff_cmp_si(ExpMat[i]->c, 1)) { /* k is torsion, nontrivial */
      coeff_set(Coefficients[newk], ExpMat[i]->c);
      Power[newk] = NewVec(Length(ExpMat[i]+1));
      Neg(Power[newk], ExpMat[i]+1);
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
      EliminateTrivialGenerators(Power[j], renumber, ExpMat);

  /*  Modify the epimorphisms: */
  for (unsigned j = 1; j <= Pres.NrGens; j++)
    EliminateTrivialGenerators(Epimorphism[j], renumber, ExpMat);
  
  /*  Modify the products: */
  for (unsigned j = 1; j <= NrPcGens; j++)
    for (unsigned l = 1; l < j; l++)
      EliminateTrivialGenerators(Product[j][l], renumber, ExpMat);

  /* Let us alter the Definitions as well. Recall that dead generator cannot
  have definition at all. It is only the right of the living ones. */
  for (unsigned i = NrPcGens + 1; i <= NrTotalGens; i++)
    if (renumber[i] >= 1) {
      Definitions[renumber[i]].g = Definitions[i].g;
      Definitions[renumber[i]].h = Definitions[i].h;
    }
  
  delete renumber;

  NrCenGens -= trivialgens;
  NrTotalGens -= trivialgens;
  
  if (Debug)
    fprintf(OutputFile, "# UpdatePcPres() finished\n");
}

void ExtendPcPres(void) {
  Dimensions = (unsigned *) realloc(Dimensions, (Class + 1) * sizeof(unsigned));
  if (Dimensions == NULL) {
    perror("EvalAllRel, Dimensions");
    exit(2);
  }
  Dimensions[Class] = NrCenGens;

  Weight = (unsigned *) realloc(Weight, (NrTotalGens + 1) * sizeof(unsigned));
  if (Weight == NULL) {
    perror("EvalAllRel, Weight");
    exit(2);
  }
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
  if (Product == NULL) {
    perror("EvalAllRel, Product");
    exit(2);
  }
  for (unsigned i = NrPcGens + 1; i <= NrTotalGens; i++) {
    Product[i] = (gpvec *) malloc(i * sizeof(gpvec));
    if (Product[i] == NULL) {
      perror("EvalAllRel, Product[i]");
      exit(2);
    }
    for (unsigned j = 1; j < i; j++) {
      Product[i][j] = NewVec(0);
      Product[i][j][0].g = EOW;
    }
  }

  NrPcGens += NrCenGens;
  NrCenGens = 0;
}
