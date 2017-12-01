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

/* v -= v[g]*w */
void ElementaryColumnOp(gpvec &v, gen g, gpvec w) {
  for (unsigned i = 0; v[i].g != EOW; i++)
    if (v[i].g == g) {
      gpvec newv = NewVec(NrTotalGens); //Length(w)+Length(v+i));
      Diff(newv, v, v[i].c, w);
      FreeVec(v); // @@@ could be optimized if we put matrix on stack
      v = ResizeVec(newv);
      break;
    }
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

  gen *renumber = new gen[NrTotalGens + 1];
  for (unsigned i = 1; i <= NrCenGens; i++)
    renumber[NrPcGens + i] = 0;

  fprintf(stderr, "%10g: rewrite powers\n", clock() /(float) CLOCKS_PER_SEC);
  for (unsigned k = NrPcGens + 1, i = 0; k <= NrTotalGens; k++)
    if (i >= NrRows || k != ExpMat[i]->g) { /* no relation for k, remains infinite */
      renumber[k] = k - trivialgens;
    } else if (coeff_cmp_si(ExpMat[i]->c, 1)) { /* k is torsion, nontrivial */
      int newk = renumber[k] = k - trivialgens;
      coeff_set(Coefficients[newk], ExpMat[i]->c);
      
      Power[newk] = NewVec(Length(ExpMat[i]+1));
      Neg(Power[newk], ExpMat[i]+1);
      i++;
    } else { /* k is trivial, and should be eliminated */
      /*  Modify the epimorphisms: */
      for (unsigned j = 1; j <= Pres.NrGens; j++)
	ElementaryColumnOp(Epimorphism[j], k, ExpMat[i]);

      /*  Products' turn: */
      for (unsigned j = 1; j <= NrPcGens; j++)
        for (unsigned l = 1; l < j; l++)
	  ElementaryColumnOp(Product[j][l], k, ExpMat[i]);

      /* The Torsions:  */
      for (unsigned j = 1; j <= NrPcGens; j++)
        if (coeff_nz(Coefficients[j]))
	  ElementaryColumnOp(Power[j], k, ExpMat[i]);
      trivialgens++;
      i++;
    }

  fprintf(stderr, "%10g: done\n", clock() /(float) CLOCKS_PER_SEC);
  /* First we eliminate the generators from the epimorphism */
  for (unsigned i = 1; i <= Pres.NrGens; i++) {
    unsigned j = 0;
    unsigned pos = 0;
    while (Epimorphism[i][j].g <= NrPcGens && Epimorphism[i][j].g != EOW)
      j++;
    pos = j;
    while (Epimorphism[i][pos].g != EOW) {
      if (renumber[Epimorphism[i][pos].g]) {
        Epimorphism[i][j].g = renumber[Epimorphism[i][pos].g];
        j++;
      }
      pos++;
      Epimorphism[i][j].g = EOW;
    }
  }

  /* Let kill all of the redundant generators from the product relations. */
  for (unsigned i = 1; i <= NrPcGens; i++)
    for (unsigned j = 1; j < i; j++) {
      unsigned k = 0;
      unsigned pos = 0;
      while (Product[i][j][k].g <= NrPcGens && Product[i][j][k].g != EOW)
        k++;
      pos = k;
      while (Product[i][j][pos].g != EOW) {
        if (renumber[Product[i][j][pos].g]) {
          Product[i][j][k].g = renumber[Product[i][j][pos].g];
          k++;
        }
        pos++;
      }
      Product[i][j][k].g = EOW;
    }

  /* Let us eliminate the generators from the power relations. */
  for (unsigned i = 1; i <= NrTotalGens; i++)
    if (coeff_nz(Coefficients[i])) {
      unsigned j = 0;
      unsigned pos = 0;
      while (Power[i][j].g <= NrPcGens && Power[i][j].g != EOW)
        j++;
      pos = j;
      while (Power[i][pos].g != EOW) {
        if (renumber[Power[i][pos].g]) {
          Power[i][j].g = renumber[Power[i][pos].g];
          j++;
        }
        pos++;
      }
      Power[i][j].g = EOW;
    }

  /* Collect the Torsions */
  for (unsigned i = NrTotalGens; i >= 1; i--)
    if (coeff_nz(Coefficients[i]))
      ShrinkCollect(Power[i]);

  /* Collect the Products */
  for (unsigned i = 1; i <= NrPcGens; i++)
    for (unsigned j = 1; j < i; j++)
      ShrinkCollect(Product[i][j]);

  /* Let us alter the Definitions as well. Recall that dead generator cannot
  have definition at all. It is only the right of the living ones. */
  for (unsigned i = NrPcGens + 1; i <= NrTotalGens; i++)
    if (renumber[i] != 0) {
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
