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

bool Graded = false;
unsigned long TorsionExp = 0;

const char USAGE[] = "Usage: lienq <options> (<inputfile> | \"-\") [<maximal class>]\n"
  "\t[-A]\ttoggle GAP output, default false\n"
  "\t[-C]\ttoggle printing compact form of multiplication table, default true\n"
  "\t[-D]\tincrease debug level\n"
  "\t[-F <outputfile>]\n"
  "\t[-G]\ttoggle graded Lie algebra, default false\n"
  "\t[-L <logfile>]\n"
  "\t[-P]\ttoggle printing definitions of basic commutators, default false\n"
  "\t[-X <exponent>]\tset exponent for p-central series, default 0\n"
  "\t[-Z]\ttoggle printing zeros in multiplication table, default false";

static const char *ordinal(unsigned n) {
  if (Class % 10 == 1 && Class != 11) return "st";
  if (Class % 10 == 2 && Class != 12) return "nd";
  if (Class % 10 == 3 && Class != 13) return "rd";
  return "th";
}

static const char *plural(unsigned n) {
  return n == 1 ? "" : "s";
}

int main(int argc, char **argv) {
  char flags[24] = "";
  int c;
  bool PrintZeros = false, PrintCompact = true, PrintDefs = false, Gap = false;
  
  while ((c = getopt (argc, argv, "ADF:GL:PX:Z")) != -1)
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
      sprintf(flags + strlen(flags), "-F '%s' ", optarg);
      break;
    case 'G':
      Graded = !Graded;
      strcat(flags, "-G ");
      break;
    case 'L':
      LogFile = fopen(optarg, "w");
      if (LogFile == NULL)
	abortprintf(1, "I can't open log file '%s'", optarg);
      sprintf(flags + strlen(flags), "-L '%s' ", optarg);
      break;
    case 'P':
      PrintDefs = !PrintDefs;
      strcat(flags, "-P ");
      break;
    case 'X':
      TorsionExp = atol(optarg);
      sprintf(flags + strlen(flags), "-X %lu ", TorsionExp);
      break;
    case 'Z':
      PrintZeros = !PrintZeros;
      strcat(flags, "-Z ");
      break;
    default:
      abortprintf(1, "Undefined flag '%c'\n%s", c, USAGE);
    }
  
  if (optind >= argc)
    abortprintf(1, "I need at least one name as input file\n%s", USAGE);

  char *InputFileName = argv[optind++];
  presentation Pres;
  unsigned UpToClass = ReadPresentation(Pres, InputFileName);
  
  if (optind < argc)
    UpToClass = atoi(argv[optind]);

  char hostname[128];
  char timestring[26];
  time_t t = time((time_t *) 0);
  strcpy(timestring, ctime(&t));
  
  gethostname(hostname, 128);
  fprintf(LogFile, "# The Lie algebra Nilpotent Quotient Program\n"
	  "# for calculating nilpotent quotients in finitely presented Lie rings by Csaba Schneider.\n");
  fprintf(LogFile, "# Program:\t%s, version %s\n", argv[0], VERSION);
  fprintf(LogFile, "# Machine:\t%s\n", hostname);
  fprintf(LogFile, "# Coefficients:\t%s\n", COEFF_ID);
  fprintf(LogFile, "# Input file:\t%s\n", InputFileName);
  fprintf(LogFile, "# Start time:\t%s", timestring);
  fprintf(LogFile, "# Class:\t%d\n", UpToClass);
  fprintf(LogFile, "# Flags:\t'%s'\n\n", flags);

#ifdef MEMCHECK
  mtrace();
#endif

  InitPcPres(Pres);

  TimeStamp("initialization");
  
  for (Class = 1; UpToClass == 0 || Class <= UpToClass; Class++) {
    unsigned oldnrpcgens = NrPcGens;

    AddNewTails(Pres); // add fresh tails

    InitStack();

    ComputeTails(); // compute other tails
    
    InitMatrix();

    Consistency(); // enforce Jacobi and Z-linearity
    
    EvalAllRel(Pres); // evaluate relations

    gpvec *rels;
    unsigned numrels;
    HermiteNormalForm(&rels, &numrels);
    
    ReducePcPres(Pres, rels, numrels); // enforce relations

    FreeMatrix();
    FreeStack();

    int newgens = NrPcGens-oldnrpcgens;
    fprintf(LogFile, "# The %d%s factor has %d generator%s", Class, ordinal(Class), newgens, plural(newgens));
    if (newgens) {
      fprintf(LogFile, " of relative order%s ", plural(newgens));
      for (unsigned i = oldnrpcgens + 1; i <= NrPcGens; i++) {
	coeff_out_str(LogFile, Exponent[i]);
	if (i != NrPcGens)
	  fprintf(LogFile, ", ");
      }
    }
    fprintf(LogFile,"\n");

    if (UpToClass == 0 && newgens == 0)
      break;
  }

  InitStack();
  if (Gap)
    PrintGAPPres(OutputFile, Pres);  
  else
    PrintPcPres(OutputFile, Pres, PrintCompact, PrintDefs, PrintZeros);
  FreeStack();

  TimeStamp("main()");

  FreePcPres(Pres);
  FreePresentation(Pres);

  return 0;
}
