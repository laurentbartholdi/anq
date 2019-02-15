/******************************************************************************
**
**                 Nilpotent Quotient for Lie Rings
** print.c                                                      Csaba Schneider
**                                                           schcs@math.klte.hu
*/

#include "nq.h"
#include <stdarg.h>
#include <vector>

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

void PrintPcPres(FILE *f, const pcpresentation &pc, const fppresentation &pres, bool PrintCompact, bool PrintDefs, bool PrintZeros) {
  fprintf(f, "<\n");

  unsigned curclass = 0;
  bool first;
  for (unsigned i = 1; i <= pc.NrPcGens; i++) {
    while (pc.Generator[i].w > curclass) {
      if (curclass++ > 0)
	fprintf(f, ";\n");
      fprintf(f, "# generators of weight %d:\n", curclass);
      first = true;
    }
    if (!first)
      fprintf(f, ", ");
    fprintf(f, "a%d", i);
    first = false;
  }
  fprintf(f, " |\n");
  
  fprintf(f, "# The epimorphism:\n");
  for (unsigned i = 1; i <= pres.NrGens; i++) {
    fprintf(f, "# %10s |-->", pres.GeneratorName[i].c_str());
    gen g = pc.Epimorphism[i][0].first;
    if (!pc.Epimorphism[i].empty() && pc.Generator[g].t == DGEN && pc.Generator[g].g == i)
      fprintf(f, ": a%d\n", g);
    else {
      fprintf(f, " ");
      PrintVec(f, pc.Epimorphism[i]);
      fprintf(f, "\n");
    }
  }
  if (PrintDefs) {
    fprintf(f, "# The definitions:\n");
    for (unsigned i = 1; i <= pc.NrPcGens; i++) {
      /* we know each element is defined as an iterated multiple of an iterated commutator of generators */
      
      fprintf(f, "#%10s a%d = ", "", i);
      switch (pc.Generator[i].t) {
      case DCOMM:
	fprintf(f, "[a%d,a%d] = ", pc.Generator[i].g, pc.Generator[i].h);
	break;
      case DPOW:
#ifdef LIEALG
	coeff_out_str(f, pc.Exponent[i]);
	fprintf(f, "*a%d = ", pc.Generator[i].g);
#else
	fprintf(f, "a%d^", pc.Generator[i].g);
	coeff_out_str(f, pc.Exponent[i]);
	fprintf(f, " = ");
#endif
	break;
      case DGEN:;
      }

      gen g = i;
      while (pc.Generator[g].t == DPOW) {
	coeff_out_str(f, pc.Exponent[g]);
	fprintf(f,"*");
	g = pc.Generator[g].g;
      }
      std::vector<gen> cv;
      while (pc.Generator[g].t == DCOMM) {
	cv.push_back(pc.Generator[g].h);
	g = pc.Generator[g].g;
      }
      fprintf(f, "[");
      for (;;) {
	if (pc.Generator[g].t != DGEN)
	  abortprintf(5, "Generator %d is not iterated multiple of iterated commutator of generators", i);
	fprintf(f, "%s", pres.GeneratorName[pc.Generator[g].g].c_str());
	if (cv.empty())
	  break;
	g = cv.back();
	cv.pop_back();
	fprintf(f, ",");
      }
      fprintf(f, "]^epimorphism\n");

    }
  }

  first = true;
  fprintf(f, "# The torsion relations:\n");
  for (unsigned i = 1; i <= pc.NrPcGens; i++) {
    if (coeff_nz_p(pc.Exponent[i])) {
      if (!first)
	  fprintf(f, ",\n");
      fprintf(f, "%10s", "");
      coeff_out_str(f, pc.Exponent[i]);
      fprintf(f, "*a%d", i);
      if (pc.Power[i].allocated()) {
	gen g = pc.Power[i][0].first;
	if (!pc.Power[i].empty()) {
	  if (pc.Generator[g].t == DPOW && pc.Generator[g].g == i)
	    fprintf(f, " =: a%d", g);
	  else {
	    fprintf(f, " = ");
	    PrintVec(f, pc.Power[i]);
	  }
	}
      }
      first = false;
    }
  }
  
  fprintf(f, "%s# The product relations:\n", first ? "" : ",\n");
  first = true;
  for (unsigned j = 1; j <= pc.NrPcGens; j++)
    for (unsigned i = 1; i < j; i++) {
      if (PrintCompact) {
	if (pc.Generator[i].t != DGEN || pc.Generator[j].t == DPOW)
	  continue;
      } else {
	if (!PrintZeros && pc.Comm[j][i].empty())
	continue;
      }  
      if (!first)
	fprintf(f, ",\n");
      fprintf(f, "%10s[a%d,a%d]", "", j, i);
      if (!pc.Comm[j][i].empty()) {
	gen g = pc.Comm[j][i][0].first;
	if (pc.Generator[g].g == j && pc.Generator[g].h == i)
	  fprintf(f, " =: a%d", g);
	else {
	  fprintf(f, " = ");
	  PrintVec(f, pc.Comm[j][i]);
	}
      }
      first = false;
    }
  
  if (!pres.Extra.empty()) {
    fprintf(f, " |\n# The extra elements:\n");
    first = true;
    for (node *n : pres.Extra) {
      hollowcvec v = vecstack.fresh();
      v.eval(pc, n);
      v.liecollect(pc);
      if (!first)
	fprintf(f, ",\n");
      fprintf(f, "%10s", ""); PrintVec(f, v);
      if (v.empty()) fprintf(f, "0*a1");
      vecstack.pop(v);
      first = false;
    }
  }
  fprintf(f, " >\n");
}

#ifdef LIEALG
template<typename V> bool PrintGAPVec(FILE *f, const V v, bool first) {
  for (auto kc : v) {
    if (first) first = false; else fprintf(f, " + ");
    coeff_out_str(f, kc.second);
    fprintf(f, "*bas[%d]", kc.first);
  }
  return first;
}

void PrintGAPPres(FILE *f, const pcpresentation &pc, const fppresentation &pres) {
  fprintf(f, "LoadPackage(\"liering\");\n"
	  "F := FreeLieRing(Integers,[");
  for (unsigned i = 1; i <= pres.NrGens; i++)
    fprintf(f, "%s\"%s\"", i > 1 ? "," : "", pres.GeneratorName[i].c_str());
  fprintf(f, "]);\n");
  fprintf(f, "L := CallFuncList(function()\n"
	  "\tlocal T, L, bas, epi, src, genimgs, eval;\n"
	  "\tT := EmptySCTable(%d,0,\"antisymmetric\");\n", pc.NrPcGens);
  for (unsigned j = 1; j <= pc.NrPcGens; j++)
    for (unsigned i = 1; i < j; i++) {
      if (!pc.Comm[j][i].empty()) {
        fprintf(f, "\tSetEntrySCTable(T,%d,%d,[", j, i);
	bool first = true;
	for (auto kc : pc.Comm[j][i]) {
	  if (!first) fprintf(f, ",");
	  coeff_out_str(f, kc.second);
	  fprintf(f, ",%d", kc.first);
	  first = false;
	}
	fprintf(f, "]);\n");
      }
    }
  fprintf(f, "\tL := LieRingByStructureConstants(ListWithIdenticalEntries(%d,0), T);\n", pc.NrPcGens);
  fprintf(f, "\tbas := Basis(L);\n"
	  "\tepi := NaturalHomomorphismByIdeal(L,LieRingIdeal(L,[");
  bool first = true;
  for (unsigned i = 1; i <= pc.NrPcGens; i++) {
    if (coeff_nz_p(pc.Exponent[i])) {
      fprintf(f, "%s-", first ? "" : ",\n\t\t");
      coeff_out_str(f, pc.Exponent[i]);
      fprintf(f, "*bas[%d]", i);
      if (pc.Power[i].allocated())
	PrintGAPVec(f, pc.Power[i], false);
      first = false;
    }
  }
  fprintf(f, "],\"basis\"));\n");

  fprintf(f, "\tgenimgs := [");
  for (unsigned i = 1; i <= pres.NrGens; i++) {
    fprintf(f, "%s(", i == 1 ? "" : ",");
    if (PrintGAPVec(f, pc.Epimorphism[i], true))
      fprintf(f, "Zero(L)");
    fprintf(f, ")^epi");
  }
  fprintf(f,"];\n");

  if (!pres.Extra.empty()) {
    fprintf(f, "\tRange(epi)!.extra := [");
    bool first = true;
    for (node *n : pres.Extra) {
      hollowcvec v = vecstack.fresh();
      v.eval(pc, n);
      v.liecollect(pc);
      fprintf(f, "%s(", first ? "" : ",");
      if (PrintGAPVec(f, v, true))
	fprintf(f,"Zero(L)");
      fprintf(f, ")^epi");
      first = false;
      vecstack.pop(v);
    }
    fprintf(f, "];\n");
  }
  
  fprintf(f, "\tL := Range(epi);\n");
  fprintf(f, "\tsrc := F;\n");
  fprintf(f, "\teval := function(expr)\n"
	  "\t\tif IsBound(expr.var) then\n"
	  "\t\t\treturn genimgs[expr.var];\n"
	  "\t\telse\n"
	  "\t\treturn eval(expr.left)*eval(expr.right);\n"
	  "\t\tfi;\n"
	  "\tend;\n");
  fprintf(f, "\tSetCanonicalProjection(L,function(elm)\n"
	  "\t\tlocal res, i;\n"
	  "\t\tif not elm in src then Error(\"Element \",elm,\" does not belong to free Lie algebra \",src); fi;\n"
	  "\t\telm := elm![1];\n"
	  "\t\tres := Zero(L);\n"
	  "\t\tfor i in [2,4..Length(elm)] do\n"
	  "\t\t\tres := res + elm[i]*eval(elm[i-1]);\n"
	  "\t\tod;\n"
	  "\t\treturn res;\n"
	  "\tend);\n");
  fprintf(f, "\treturn L;\n"
	  "end,[]);\n");
}
#else
template<typename V> void PrintGAPVec(FILE *f, const V v) {
  bool first = true;
  for (auto kc : v) {
    if (first) first = false; else fprintf(f, "*");
    fprintf(f, "g[%u]^", kc.first);
    coeff_out_str(f, kc.second);
  }
  if (first)
    fprintf(f, "One(F)");
}

void PrintGAPPres(FILE *f, const pcpresentation &pc, const fppresentation &pres) {
  fprintf(f, "LoadPackage(\"nq\");\n"
	  "F := FreeGroup(IsSyllableWordsFamily,[");
  for (unsigned i = 1; i <= pres.NrGens; i++)
    fprintf(f, "%s\"%s\"", i > 1 ? "," : "", pres.GeneratorName[i].c_str());
  fprintf(f, "]);\n");

  fprintf(f, "G := CallFuncList(function()\n"
	  "\tlocal F, c, g;\n"
	  "\tF := FreeGroup(%d,\"a\");\n"
	  "\tg := GeneratorsOfGroup(F);\n"
	  "\tc := FromTheLeftCollector(%d);\n", pc.NrPcGens, pc.NrPcGens);
  for (unsigned i = 1; i <= pc.NrPcGens; i++)
    if (coeff_nz_p(pc.Exponent[i])) {
      fprintf(f, "\tSetRelativeOrder(c,%u,", i);
      coeff_out_str(f, pc.Exponent[i]);
      fprintf(f, ");\n\tSetPower(c,%u,", i);
      PrintGAPVec(f, pc.Power[i]);
      fprintf(f, ");\n");
    }
  for (unsigned j = 1; j <= pc.NrPcGens; j++)
    for (unsigned i = 1; i < j; i++)
      if (!pc.Comm[j][i].empty()) {
        fprintf(f, "\tSetCommutator(c,%u,%u,", j, i);
	PrintGAPVec(f, pc.Comm[j][i]);
	fprintf(f, ");\n");
      }
  fprintf(f, "\n\tF := PcpGroupByCollector(c);\n");
  fprintf(f, "\tg := GeneratorsOfGroup(F);\n");
  fprintf(f, "\tSetEpimorphismFromFreeGroup(G,GroupHomomorphismByImages(F,G,[");
  for (unsigned i = 1; i <= pres.NrGens; i++) {
    if (i > 1) fprintf(f, ",");
    PrintGAPVec(f, pc.Epimorphism[i]);
  }
  fprintf(f, "]));\n");
  fprintf(f, "\treturn PcpGroupByCollector(c);\n"
	  "end,[]);\n");
}
#endif
