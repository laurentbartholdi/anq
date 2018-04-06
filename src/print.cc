/******************************************************************************
**
**                 Nilpotent Quotient for Lie Rings
** print.c                                                      Csaba Schneider
**                                                           schcs@math.klte.hu
*/

#include "lienq.h"
#include <stdarg.h>

/*
** This file contains the print routines that are necessary to be able to
** print the result in a nice format.
*/

clock_t ClockStart;

void abortprintf(int errorcode, const char *format, ...) {
  va_list ap;
  va_start(ap, format);
  
  vfprintf(stderr, format, ap);
  fprintf(stderr,"\n");

  if (OutputFile != stdout)
    vfprintf(OutputFile, format, ap), fprintf(OutputFile,"\n");

  va_end(ap);
  
  exit(errorcode);
}

void TimeStamp(const char *s) {
  static clock_t lastclock = 0;

  if (Debug) {
    clock_t newclock = clock();
    fprintf(OutputFile, "# %s finished, %.3gs\n", s, (newclock-lastclock) / (float)CLOCKS_PER_SEC);
    fflush(OutputFile);
    lastclock = newclock;
  }
}

void PrintVec(gpvec gv) {
  for (unsigned i = 0; gv[i].g != EOW; i++) {
    if (i) fprintf(OutputFile, " + ");
    coeff_out_str(OutputFile, gv[i].c);
    fprintf(OutputFile, "*a%d", gv[i].g);
  }
}

void PrintPcPres(presentation &Pres) {
  fprintf(OutputFile, "<");

  unsigned curclass = 0;
  for (unsigned i = 1; i <= NrPcGens; i++) {
    if (Weight[i] > curclass) {
      curclass = Weight[i];
      fprintf(OutputFile, "\n# Weight %d:\n", curclass);
    }
    fprintf(OutputFile, " a%d%s", i, i < NrPcGens ? "," : "");
  }
  fprintf(OutputFile, " |\n");
  
  fprintf(OutputFile, "# The epimorphism:\n");
  for (unsigned i = 1; i <= Pres.NrGens; i++) {
    gen g = Epimorphism[i]->g;
    fprintf(OutputFile, "# %10s |-->", Pres.GeneratorName[i]);
    if (g && isimggen(g) && i == Definition[g].g)
      fprintf(OutputFile, ": a%d\n", g);
    else {
      fprintf(OutputFile, " ");
      PrintVec(Epimorphism[i]);
      fprintf(OutputFile, "\n");
    }
  }
  if (PrintDefs) {
    fprintf(OutputFile, "# The definitions:\n");
    for (unsigned i = 1; i <= NrTotalGens; i++)
      if (iscommgen(i)) {
	gen cv[Weight[i] + 1], g = i;
	for (unsigned pos = Weight[g]; Weight[g] > 1; pos--) {
	  if (!iscommgen(g))
	    abortprintf(5, "Iterated definition of generator %d does not involve commutators and weight-1 generators", i);

	  cv[pos] = Definition[g].h;
	  g = Definition[g].g;
	}
	cv[1] = g;
	fprintf(OutputFile, "#%10s a%d = [a%d,a%d] = [", "", i, Definition[i].g, Definition[i].h);
	for (unsigned j = 1; j <= Weight[i]; j++)
	  fprintf(OutputFile, "a%d%s", cv[j], j == Weight[i] ? "]\n" : ",");
      } else {
	gen g = Definition[i].g;
	if (0 < (int)g)
	  fprintf(OutputFile, "#%10s a%d = (%s)^epimorphism\n", "", i, Pres.GeneratorName[g]);
	else {
	  fprintf(OutputFile, "#%10s a%d = ", "", i);
	  coeff_out_str(OutputFile, Exponent[-g]);
	  fprintf(OutputFile, "*a%d", -g);
	}
      }
  }

  bool first = true;
  fprintf(OutputFile, "# The torsion relations:\n");
  for (unsigned i = 1; i <= NrPcGens; i++) {
    if (coeff_nz_p(Exponent[i])) {
      if (!first)
	  fprintf(OutputFile, ",\n");
      fprintf(OutputFile, "%10s", "");
      coeff_out_str(OutputFile, Exponent[i]);
      fprintf(OutputFile, "*a%d", i);
      if (Power[i] != NULL && Power[i]->g != EOW) {
	if (ispowergen(Power[i]->g))
	  fprintf(OutputFile, " =: a%d", Power[i]->g);
	else {
	  fprintf(OutputFile, " = ");
	  PrintVec(Power[i]);
	}
      }
      first = false;
    }
  }

  first = true;
  for (unsigned j = 1; j <= NrPcGens; j++)
    for (unsigned i = 1; i < j; i++) {
      gen g = Product[j][i]->g;
      if (PrintZeros || g != EOW) {
	fprintf(OutputFile, ",\n");
	if (first)
	  fprintf(OutputFile, "# The product relations:\n");
        fprintf(OutputFile, "%10s[ a%d, a%d ]", "", j, i);
        if (g != EOW) {
	  if (Definition[g].g == j && Definition[g].h == i)
	    fprintf(OutputFile, " =: a%d", Product[j][i]->g);
	  else {
	    fprintf(OutputFile, " = ");
	    PrintVec(Product[j][i]);
	  }
        }
	first = false;
      }
    }
  
  if (Pres.NrExtra > 0) {
    fprintf(OutputFile, " |\n# The extra elements:\n");
    first = true;
    gpvec v = FreshVec();
    for (unsigned i = 0; i < Pres.NrExtra; i++) {
      gpvec temp = FreshVec();
      EvalRel(temp, Pres.Extra[i]);
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
