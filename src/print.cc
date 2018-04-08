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

  if (LogFile != stdout)
    vfprintf(LogFile, format, ap), fprintf(LogFile,"\n");

  va_end(ap);
  
  exit(errorcode);
}

void TimeStamp(const char *s) {
  static clock_t lastclock = 0;

  if (Debug) {
    clock_t newclock = clock();
    fprintf(LogFile, "# %s finished, %.3gs\n", s, (newclock-lastclock) / (float)CLOCKS_PER_SEC);
    fflush(LogFile);
    lastclock = newclock;
  }
}

void PrintVec(FILE *f, gpvec gv) {
  for (unsigned i = 0; gv[i].g != EOW; i++) {
    if (i) fprintf(f, " + ");
    coeff_out_str(f, gv[i].c);
    fprintf(f, "*a%d", gv[i].g);
  }
}

void PrintPcPres(FILE *f, presentation &Pres) {
  fprintf(f, "<");

  unsigned curclass = 0;
  for (unsigned i = 1; i <= NrPcGens; i++) {
    if (Weight[i] > curclass) {
      curclass = Weight[i];
      fprintf(f, "\n# Weight %d:\n", curclass);
    }
    fprintf(f, " a%d%s", i, i < NrPcGens ? "," : "");
  }
  fprintf(f, " |\n");
  
  fprintf(f, "# The epimorphism:\n");
  for (unsigned i = 1; i <= Pres.NrGens; i++) {
    gen g = Epimorphism[i]->g;
    fprintf(f, "# %10s |-->", Pres.GeneratorName[i]);
    if (g && isimggen(g) && i == Definition[g].g)
      fprintf(f, ": a%d\n", g);
    else {
      fprintf(f, " ");
      PrintVec(f, Epimorphism[i]);
      fprintf(f, "\n");
    }
  }
  if (PrintDefs) {
    fprintf(f, "# The definitions:\n");
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
	fprintf(f, "#%10s a%d = [a%d,a%d] = [", "", i, Definition[i].g, Definition[i].h);
	for (unsigned j = 1; j <= Weight[i]; j++)
	  fprintf(f, "a%d%s", cv[j], j == Weight[i] ? "]\n" : ",");
      } else {
	gen g = Definition[i].g;
	if (0 < (int)g)
	  fprintf(f, "#%10s a%d = (%s)^epimorphism\n", "", i, Pres.GeneratorName[g]);
	else {
	  fprintf(f, "#%10s a%d = ", "", i);
	  coeff_out_str(f, Exponent[-g]);
	  fprintf(f, "*a%d", -g);
	}
      }
  }

  bool first = true;
  fprintf(f, "# The torsion relations:\n");
  for (unsigned i = 1; i <= NrPcGens; i++) {
    if (coeff_nz_p(Exponent[i])) {
      if (!first)
	  fprintf(f, ",\n");
      fprintf(f, "%10s", "");
      coeff_out_str(f, Exponent[i]);
      fprintf(f, "*a%d", i);
      if (Power[i] != NULL && Power[i]->g != EOW) {
	if (ispowergen(Power[i]->g))
	  fprintf(f, " =: a%d", Power[i]->g);
	else {
	  fprintf(f, " = ");
	  PrintVec(f, Power[i]);
	}
      }
      first = false;
    }
  }
  fprintf(f, "%s# The product relations:\n", first ? "" : ",\n");

  first = true;
  for (unsigned j = 1; j <= NrPcGens; j++)
    for (unsigned i = 1; i < j; i++) {
      gen g = Product[j][i]->g;
      if (PrintZeros || g != EOW) {
	if (!first)
          fprintf(f, ",\n");
        fprintf(f, "%10s[ a%d, a%d ]", "", j, i);
        if (g != EOW) {
	  if (Definition[g].g == j && Definition[g].h == i)
	    fprintf(f, " =: a%d", Product[j][i]->g);
	  else {
	    fprintf(f, " = ");
	    PrintVec(f, Product[j][i]);
	  }
        }
	first = false;
      }
    }
  
  if (Pres.NrExtra > 0) {
    fprintf(f, " |\n# The extra elements:\n");
    first = true;
    gpvec v = FreshVec();
    for (unsigned i = 0; i < Pres.NrExtra; i++) {
      gpvec temp = FreshVec();
      EvalRel(temp, Pres.Extra[i]);
      Collect(v, temp);
      PopVec();
      if (!first)
	fprintf(f, ",\n");
      fprintf(f, "%10s", ""); PrintVec(f, v);
      if (v->g == EOW) fprintf(f, "0*a1");
      first = false;
    }
    PopVec();
  }
  fprintf(f, " >\n");
}

void PrintGAPPres(FILE *f, presentation &Pres) {
  fprintf(f, "LoadPackage(\"liering\");\n"
	  "F := FreeLieRing(Integers,[");
  for (unsigned i = 1; i <= Pres.NrGens; i++)
    fprintf(f, "%s\"%s\"", i > 1 ? "," : "", Pres.GeneratorName[i]);
  fprintf(f, "]);\n"
	  "L := CallFuncList(function()\n"
	  "\tlocal T, L, bas, epi, src, genimgs, eval;\n"
	  "\tT := EmptySCTable(%d,0,\"antisymmetric\");\n", NrPcGens);
  for (unsigned j = 1; j <= NrPcGens; j++)
    for (unsigned i = 1; i < j; i++) {
      gen g = Product[j][i]->g;
      if (g != EOW) {
        fprintf(f, "\tSetEntrySCTable(T,%d,%d,[", j, i);
	bool first = true;
	for (gpvec v = Product[j][i]; v->g != EOW; v++) {
	  if (!first) fprintf(f, ",");
	  coeff_out_str(f, v->c);
	  fprintf(f, ",%d", v->g);
	  first = false;
	}
	fprintf(f, "]);\n");
      }
    }
  fprintf(f, "\tL := LieRingByStructureConstants(ListWithIdenticalEntries(%d,0), T);\n", NrPcGens);
  fprintf(f, "\tbas := Basis(L);\n"
	  "\tepi := NaturalHomomorphismByIdeal(L,LieRingIdeal(L,[");
  bool first = true;
  for (unsigned i = 1; i <= NrPcGens; i++) {
    if (coeff_nz_p(Exponent[i])) {
      fprintf(f, "%s-", first ? "" : ",\n\t\t");
      coeff_out_str(f, Exponent[i]);
      fprintf(f, "*bas[%d]", i);
      if (Power[i] != NULL && Power[i]->g != EOW) {
	for (gpvec v = Power[i]; v->g != EOW; v++) {
	  fprintf(f, " + ");
	  coeff_out_str(f, v->c);
	  fprintf(f, "*bas[%d]", v->g);
	  first = false;
	}
      }
      first = false;
    }
  }
  fprintf(f, "],\"basis\"));\n");

  fprintf(f, "\tgenimgs := [");
  for (unsigned i = 1; i <= Pres.NrGens; i++) {
    fprintf(f, "%s(", i == 1 ? "" : ",");
    bool first = true;
    for (gpvec v = Epimorphism[i]; v->g != EOW; v++) {
      fprintf(f, "%s", first ? "" : " + ");
      coeff_out_str(f, v->c);
      fprintf(f, "*bas[%d]", v->g);
      first = false;
    }
    fprintf(f, ")^epi");
  }
  fprintf(f,"];\n");

  if (Pres.NrExtra > 0) {
    fprintf(f, "\tRange(epi)!.extra := [");
    gpvec v = FreshVec();
    for (unsigned i = 0; i < Pres.NrExtra; i++) {
      gpvec temp = FreshVec();
      EvalRel(temp, Pres.Extra[i]);
      Collect(v, temp);
      PopVec();
      fprintf(f, "%s(", i == 0 ? "" : ",");
      bool first = true;
      for (gpvec p = v; p->g != EOW; p++) {
	fprintf(f, "%s", first ? "" : " + ");
	coeff_out_str(f, p->c);
	fprintf(f, "*bas[%d]", p->g);
	first = false;
      }
      if (first)
	fprintf(f,"Zero(L)");
      fprintf(f, ")^epi");
    }
    PopVec();
    fprintf(f, "];\n");
  }
  
  fprintf(f, "\tL := Range(epi);\n"
	  "\tsrc := F;\n"
	  "\teval := function(expr)\n"
	  "\t\tif IsBound(expr.var) then\n"
	  "\t\t\treturn genimgs[expr.var];\n"
	  "\t\telse\n"
	  "\t\treturn eval(expr.left)*eval(expr.right);\n"
	  "\t\tfi;\n"
	  "\tend;\n"
	  "\tSetCanonicalProjection(L,function(elm)\n"
	  "\t\tlocal res, i;\n"
	  "\t\tif not elm in src then Error(\"Element \",elm,\" does not belong to free Lie algebra \",src); fi;\n"
	  "\t\telm := elm![1];\n"
	  "\t\tres := Zero(L);\n"
	  "\t\tfor i in [2,4..Length(elm)] do\n"
	  "\t\t\tres := res + elm[i]*eval(elm[i-1]);\n"
	  "\t\tod;\n"
	  "\t\treturn res;\n"
	  "\tend);\n"
	  "\treturn L;\n"
	  "end,[]);\n");
}
