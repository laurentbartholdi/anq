/******************************************************************************
**
**                 Nilpotent Quotient for Lie Rings
** print.c                                                      Csaba Schneider
**                                                           schcs@math.klte.hu
*/

#include "lienq.h"

/*
** This file contains the print routins that are necessary to be able to
** print the result in a nice format.
*/

void PrintGpVec(gpvec gv) {
  for (unsigned i = 0; gv[i].g != EOW; i++)
    fprintf(OutputFile, "%s%ld*a%d", i ? " + " : "", coeff_get_si(gv[i].c), gv[i].g);
}

void PrintCoeffVec(coeffvec cv) {
  bool first = true;
  for (unsigned i = 1; i <= NrTotalGens; i++)
    if (coeff_nz(cv[i])) {
      fprintf(OutputFile, "%s%ld*a%d", first ? "" : " + ", coeff_get_si(cv[i]), i);
      first = false;
    }
}

static void Indent(int n)

{
  while (n-- > 0)
    fprintf(OutputFile, " ");
}

void Filline() {
  int i;
  putc(' ', OutputFile);
  for (i = 1; i <= 78; i++)
    putc('_', OutputFile);
  putc('\n', OutputFile);
}

void PrintEpim() {
  Indent(2);
  fprintf(OutputFile, "# The epimorphism:\n");
  for (unsigned i = 1; i <= Pres.NrGens; i++) {
    Indent(10);
    fprintf(OutputFile, "# %s |--> ", Pres.Generators[i]);
    PrintGpVec(Epimorphism[i]);
    fprintf(OutputFile, "\n");
  }
  fprintf(OutputFile, "\n");
}

static void PrintGens() {
  Indent(3);
  for (unsigned i = 1; i <= NrPcGens; i++)
    fprintf(OutputFile, "a%d%s", i, i < NrPcGens ? ", " : "");
}

void PrintPcPres() {
  unsigned i, j, products;

  fprintf(OutputFile, "  <");
  PrintGens();
  fprintf(OutputFile, "  |\n");
  PrintEpim();
  Indent(2);
  fprintf(OutputFile, "# The torsion relations:\n");

  for (unsigned i = 1; i <= NrPcGens; i++) {
    if (coeff_nz(Coefficients[i])) {

      Indent(10);
      fprintf(OutputFile, "%ld*a%d", coeff_get_si(Coefficients[i]), i);
      if (Power[i][0].g != EOW) {
        fprintf(OutputFile, " = ");
        PrintGpVec(Power[i]);
      }
      fprintf(OutputFile, ",\n");
    }
  }

  fprintf(OutputFile, "\n\n");
  Indent(2);
  fprintf(OutputFile, "# The product relations:\n");

  if (PrintZeros)
    products = NrPcGens * (NrPcGens - 1) / 2;
  else
    for (products = 0, i = 1; i <= NrPcGens; i++)
      for (j = 1; j < i; j++)
        if (Product[i][j][0].g != EOW)
          products++;

  for (j = 1; j <= NrPcGens; j++)
    for (i = 1; i < MIN(NrPcGens - 1, j); i++)
      if (PrintZeros || Product[j][i][0].g != EOW) {
        Indent(10);
        fprintf(OutputFile, "[  a%d,  a%d ]", j, i);
        if (Product[j][i][0].g != EOW) {
          fprintf(OutputFile, " = ");
          PrintGpVec(Product[j][i]);
        }
        if (--products > 0)
          fprintf(OutputFile, ",\n");
      }
  if (PrintZeros ||
      (NrPcGens > 1 && Product[NrPcGens][NrPcGens - 1][0].g != EOW)) {
    Indent(10);
    fprintf(OutputFile, "[  a%d,  a%d ]", NrPcGens, NrPcGens - 1);
    if (Product[NrPcGens][NrPcGens - 1][0].g != EOW) {
      fprintf(OutputFile, " = ");
      PrintGpVec(Product[NrPcGens][NrPcGens - 1]);
    }
  }
  fprintf(OutputFile, "   >\n");
}

void PrintMat(coeffvec *M) {
  for (unsigned i = 0; i <= NrRows - 1; i++) {
    fprintf(OutputFile, "# ");
    for (unsigned j = 1; j <= NrCenGens; j++)
      fprintf(OutputFile, "%ld  ", coeff_get_si(M[i][j]));
    fprintf(OutputFile, "\n");
  }
}

void PrintDef() {
  for (unsigned i = 1; i <= NrPcGens; i++)
    if (Definitions[i].h == 0)
      fprintf(OutputFile, "# a%d = (%d)epim\n", i, Definitions[i].g);
    else
      fprintf(OutputFile, "# a%d = [ %d, %d ]\n", i, Definitions[i].g,
              Definitions[i].h);
}

void PrintDefinitions() {
  for (unsigned i = 1; i <= NrTotalGens; i++)
    if (Definitions[i].h > 0) {
      gen *cv = (gen *)malloc((Weight[i] + 1) * sizeof(gen));
      ComputePcGen(i, cv, 1);
      Indent(2);
      fprintf(OutputFile, "# a%d = [ ", i);
      for (unsigned j = 1; j <= Weight[i] - 1; j++)
        fprintf(OutputFile, "%s, ", Pres.Generators[cv[j]]);
      fprintf(OutputFile, "%s ]\n", Pres.Generators[cv[Weight[i]]]);
      free(cv);
    }
}
