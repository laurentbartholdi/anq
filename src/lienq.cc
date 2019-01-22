/******************************************************************************
**
**                 Nilpotent Quotient for Lie Rings
** lienq.c                                                      Csaba Schneider
**                                                           schcs@math.klte.hu
*/

#include "lienq.h"
#include <string.h>
#include <sys/types.h>
#include <unistd.h>
#ifdef MEMCHECK
#include <mcheck.h>
#endif

FILE *OutputFile = stdout, *LogFile = stdout;
unsigned Debug = 0;

const char USAGE[] = "Usage: lienq <options> [<inputfile>]\n"
  "(with no input file, presentation is read from STDIN)\n"
  "\t[-A]\ttoggle GAP output, default false\n"
  "\t[-C]\ttoggle printing compact form of multiplication table, default true\n"
  "\t[-D]\tincrease debug level\n"
  "\t[-F <outputfile>]\n"
  "\t[-G]\ttoggle graded Lie algebra, default false\n"
  "\t[-L <logfile>]\n"
  "\t[-N <nilpotency class>]\n"
  "\t[-P]\ttoggle printing definitions of basic commutators, default false\n"
  "\t[-W <maximal weight>]\n"
  "\t[-X <exponent>]\tset exponent for p-central series, default 0\n"
  "\t[-Z]\ttoggle printing zeros in multiplication table, default false";

const char EXTENDEDUSAGE[] = "Presentation format:\n"
  "\tpresentation = '<' (';'* gen (',' gen)*)* '|' exprlist? ('|' exprlist?)? '>'\n"
  "(each ';' in presentation increases weight, starting from 1.)\n"
  "(second exprlist gives relations. third exprlist is evaluated in quotient)\n"
  "\tgen = '[a-zA-Z_.]' '[a-zA-Z0-9_.]'*\n"
  "\texprlist = expr (',' expr)*\n"
  "\texpr = term | term ('*' | '/' | '^' | '+' | '-' | '=' | ':=' | '=:') term\n"
  "\tterm = '-' expr | '~' expr | '(' expr ')' | '[' exprlist ']' | '{' exprlist '}' | number | gen (with usual precedence)\n"
  "\tnumber = [0-9]+ (if starting with 0 then in given base, otherwise base 10)\n";

static const char *ordinal(unsigned n) {
  if (n % 10 == 1 && n != 11) return "st";
  if (n % 10 == 2 && n != 12) return "nd";
  if (n % 10 == 3 && n != 13) return "rd";
  return "th";
}

static const char *plural(unsigned n) {
  return n == 1 ? "" : "s";
}

int main(int argc, char **argv) {
  char flags[1000] = "";
  int c;
  bool PrintZeros = false, PrintCompact = true, PrintDefs = false, Gap = false, Graded = false, PAlgebra = false;
  coeff TorsionExp;
  coeff_init_set_si(TorsionExp, 0);
  unsigned MaxWeight = INFINITY, NilpotencyClass = INFINITY;
  const char *InputFileName;
  
  while ((c = getopt (argc, argv, "ACDF:GhL:N:PX:W:Z")) != -1)
    switch (c) {
    case 'A':
      Gap = !Gap;
      strcat(flags, "-A ");
      break;
    case 'C':
      PrintCompact = !PrintCompact;
      strcat(flags, "-C ");
      break;
    case 'D':
      Debug++;
      strcat(flags, "-D ");
      break;
    case 'F':
      OutputFile = fopen(optarg, "w");
      if (OutputFile == NULL)
	abortprintf(1, "I can't open output file '%s'", optarg);
      sprintf(flags + strlen(flags), "-F'%s' ", optarg);
      break;
    case 'G':
      Graded = !Graded;
      strcat(flags, "-G ");
      break;
    case 'h':
      printf("%s\n\n%s", USAGE, EXTENDEDUSAGE);
      return 0;
    case 'L':
      LogFile = fopen(optarg, "w");
      if (LogFile == NULL)
	abortprintf(1, "I can't open log file '%s'", optarg);
      sprintf(flags + strlen(flags), "-L'%s' ", optarg);
      break;
    case 'N':
      NilpotencyClass = atoi(optarg);
      sprintf(flags + strlen(flags), "-N%u ", NilpotencyClass);
      break;
    case 'P':
      PrintDefs = !PrintDefs;
      strcat(flags, "-P ");
      break;
    case 'X':
      PAlgebra = true;
      // replace by: coeff_get_str !!!
      coeff_set_si(TorsionExp, atol(optarg));
      sprintf(flags + strlen(flags), "-X%lu ", coeff_get_si(TorsionExp));
      break;
    case 'W':
      MaxWeight = atoi(optarg);
      sprintf(flags + strlen(flags), "-W%u ", MaxWeight);
      break;
    case 'Z':
      PrintZeros = !PrintZeros;
      strcat(flags, "-Z ");
      break;
    default:
      abortprintf(1, "Undefined flag '%c'\n%s", c, USAGE);
    }
  
  if (optind == argc)
    InputFileName = "";
  else if (optind == argc-1)
    InputFileName = argv[optind];
  else
    abortprintf(1, "I need precisely at most one argument as input filename\n%s", USAGE);

  presentation fppres;
  ReadPresentation(fppres, InputFileName);
  
  char hostname[128];
  gethostname(hostname, 128);
  
  time_t t = time((time_t *) 0);
  char timestring[128];
  strftime(timestring, 128, "%c", localtime(&t));
  
  fprintf(LogFile, "# The Lie algebra Nilpotent Quotient Program, by Csaba Schneider & Laurent Bartholdi\n");
  fprintf(LogFile, "# Version %s, coefficients %s\n", VERSION, COEFF_ID);
  fprintf(LogFile, "# \"%s %s%s\" started %s on %s\n", argv[0], flags, InputFileName, timestring, hostname);
  fprintf(LogFile, "# nilpotency class %u; maximal weight %u\n\n", NilpotencyClass, MaxWeight);

#ifdef MEMCHECK
  mtrace();
#endif

  pcpresentation pc;
  
  InitPcPres(pc, fppres, Graded, PAlgebra, TorsionExp, NilpotencyClass);

  TimeStamp("initialization");
  
  for (pc.Class = 1; pc.Class <= MaxWeight; pc.Class++) {
    unsigned oldnrpcgens = pc.NrPcGens;

    AddNewTails(pc, fppres); // add fresh tails

    InitStack();

    ComputeTails(pc); // compute other tails
    
    InitRelMatrix(pc, NrTotalGens-pc.NrPcGens);

    Consistency(pc); // enforce Jacobi and Z-linearity
    
    EvalAllRel(pc, fppres); // evaluate relations

    relmatrix rels = GetRelMatrix();
    
    ReducePcPres(pc, fppres, rels); // enforce relations

    FreeRelMatrix();
    FreeStack();

    int newgens = pc.NrPcGens-oldnrpcgens;
    fprintf(LogFile, "# The %d%s factor has %d generator%s", pc.Class, ordinal(pc.Class), newgens, plural(newgens));
    if (newgens) {
      fprintf(LogFile, " of relative order%s ", plural(newgens));
      for (unsigned i = oldnrpcgens + 1; i <= pc.NrPcGens; i++) {
	coeff_out_str(LogFile, pc.Exponent[i]);
	if (i != pc.NrPcGens)
	  fprintf(LogFile, ", ");
      }
    }
    fprintf(LogFile,"\n");

    if (MaxWeight == INFINITY && newgens == 0)
      break;
  }

  InitStack();
  if (Gap)
    PrintGAPPres(OutputFile, pc, fppres);  
  else
    PrintPcPres(OutputFile, pc, fppres, PrintCompact, PrintDefs, PrintZeros);
  FreeStack();

  TimeStamp("main()");

  FreePcPres(pc, fppres);
  FreePresentation(fppres);
  coeff_clear(TorsionExp);
  
  return 0;
}
