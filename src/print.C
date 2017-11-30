/******************************************************************************
**
**                 Nilpotent Quotient for Lie Rings
** print.c                                                      Csaba Schneider
**                                                           schcs@math.klte.hu
*/

#include "lienq.h"

/*
** This file contains the print routines that are necessary to be able to
** print the result in a nice format.
*/

void PrintVec(gpvec gv) {
  for (unsigned i = 0; gv[i].g != EOW; i++)
    fprintf(OutputFile, "%s%ld*a%d", i ? " + " : "", coeff_get_si(gv[i].c), gv[i].g);
}

void PrintPcPres(void) {
  fprintf(OutputFile, "<");

  for (unsigned i = 1; i <= NrPcGens; i++)
    fprintf(OutputFile, " a%d%s", i, i < NrPcGens ? "," : "");
  fprintf(OutputFile, " |\n");
  
  fprintf(OutputFile, "# The epimorphism:\n");
  for (unsigned i = 1; i <= Pres.NrGens; i++) {
    fprintf(OutputFile, "# %10s |--> ", Pres.Generators[i]);
    PrintVec(Epimorphism[i]);
    fprintf(OutputFile, "\n");
  }
  if (PrintDefs) {
    fprintf(OutputFile, "# The definitions:\n");
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
    fprintf(OutputFile, "# And again:\n");
    for (unsigned i = 1; i <= NrPcGens; i++)
      if (Definitions[i].h == 0)
	fprintf(OutputFile, "# a%d = (%d)epim\n", i, Definitions[i].g);
      else
	fprintf(OutputFile, "# a%d = [ %d, %d ]\n", i, Definitions[i].g,
		Definitions[i].h);
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
        PrintVec(Power[i]);
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
          PrintVec(Product[j][i]);
        }
	first = false;
      }    

  if (Pres.NrExtraRels > 0) {
    fprintf(OutputFile, " |\n# The extra elements:\n");
    first = true;
    gpvec v = FreshVec();
    for (unsigned i = 0; i < Pres.NrExtraRels; i++) {
      gpvec temp = FreshVec();
      EvalRel(temp, Pres.ExtraRelators[i]);
      Collect(v, temp);
      PopVec();
      if (!first)
	fprintf(OutputFile, ",\n");
      fprintf(OutputFile, "%10s", ""); PrintVec(v);
      if (v->g == EOW) fprintf(OutputFile, "0*a1");
      first = false;
    }
    PopVec();
  }
  fprintf(OutputFile, " >\n");
}
