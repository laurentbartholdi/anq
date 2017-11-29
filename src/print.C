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

void PrintPcPres(void) {
  fprintf(OutputFile, "<");

  for (unsigned i = 1; i <= NrPcGens; i++)
    fprintf(OutputFile, " a%d%s", i, i < NrPcGens ? "," : "");
  fprintf(OutputFile, " |\n");
  
  fprintf(OutputFile, "# The epimorphism:\n");
  for (unsigned i = 1; i <= Pres.NrGens; i++) {
    fprintf(OutputFile, "# %10s |--> ", Pres.Generators[i]);
    PrintGpVec(Epimorphism[i]);
    fprintf(OutputFile, "\n");
  }

  bool first = true;
  fprintf(OutputFile, "# The torsion relations:\n");
  for (unsigned i = 1; i <= NrPcGens; i++) {
    if (coeff_nz(Coefficients[i])) {
      if (!first)
	  fprintf(OutputFile, ",\n");
      fprintf(OutputFile, "%10s%ld*a%d", "", coeff_get_si(Coefficients[i]), i);
      if (Power[i][0].g != EOW) {
        fprintf(OutputFile, " = ");
        PrintGpVec(Power[i]);
      }
      first = false;
    }
  }

  first = true;
  for (unsigned j = 1; j <= NrPcGens; j++)
    for (unsigned i = 1; i < j; i++)
      if (PrintZeros || Product[j][i][0].g != EOW) {
	fprintf(OutputFile, ",\n");
	if (first)
	  fprintf(OutputFile, "# The product relations:\n");
        fprintf(OutputFile, "%10s[ a%d, a%d ]", "", j, i);
        if (Product[j][i][0].g != EOW) {
          fprintf(OutputFile, " = ");
          PrintGpVec(Product[j][i]);
        }
	first = false;
      }    

  if (Pres.NrExtraRels > 0) {
    fprintf(OutputFile, " |\n# The extra elements:\n");
    first = true;
    for (unsigned i = 0; i < Pres.NrExtraRels; i++) {
      gpvec gv = NewGpVec(NrTotalGens);
      EvalRel(gv, Pres.ExtraRelators[i]);
      coeffvec cv = GpVecToCoeffVec(gv);
      Collect(cv);
      if (!first)
	fprintf(OutputFile, ",\n");
      fprintf(OutputFile, "%10s", ""); PrintCoeffVec(cv);
      if (RealLength(cv) == 0) fprintf(OutputFile, "0*a1");
      FreeCoeffVec(cv);
      FreeGpVec(gv);
      first = false;
    }
  }
  fprintf(OutputFile, " >\n");
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
      fprintf(OutputFile, "# a%d = [ ", i);
      for (unsigned j = 1; j <= Weight[i] - 1; j++)
        fprintf(OutputFile, "%s, ", Pres.Generators[cv[j]]);
      fprintf(OutputFile, "%s ]\n", Pres.Generators[cv[Weight[i]]]);
      free(cv);
    }
}
