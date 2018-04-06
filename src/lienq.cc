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

FILE *OutputFile = stdout;

const char USAGE[] = "Usage: lienq [-A]\ttoggle GAP output, default false\n"
  "\t[-D]\tincrease debug level\n"
  "\t[-F <outputfile>]\n"
  "\t[-G]toggle graded Lie algebra, default false\n"
  "\t[-P]\ttoggle printing definitions of basic commutators, default false\n"
  "\t[-X <exponent>]\tset exponent for p-central series, default 0\n"
  "\t[-Z]\ttoggle printing of zeros in multiplication table, default false\n"
  "\t<inputfile>\n"
  "\t[<maximal class>]";

bool PrintZeros = false, Graded = false, Gap = false, PrintDefs = false;
unsigned Debug = 0;
unsigned long TorsionExp = 0;

int main(int argc, char **argv) {
  char flags[24] = "";
  int c;
  
  while ((c = getopt (argc, argv, "ADF:GPX:Z")) != -1)
    switch (c) {
    case 'A':
      Gap = !Gap;
      strcat(flags, "-A ");
      break;
    case 'D':
      Debug++;
      strcat(flags, "-D ");
      break;
    case 'F':
      OutputFile = fopen(optarg, "w");
      if (OutputFile == NULL)
	abortprintf(1, "I can't open the output file '%s'", optarg);
      sprintf(flags + strlen(flags), "-F '%s' ", optarg);
      break;
    case 'G':
      Graded = !Graded;
      strcat(flags, "-G ");
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
  fprintf(OutputFile, "# The Lie algebra Nilpotent Quotient Program\n"
	  "# for calculating nilpotent quotients in finitely presented Lie rings by Csaba Schneider.\n");
  fprintf(OutputFile, "# Program:\t%s, version %s\n", argv[0], VERSION);
  fprintf(OutputFile, "# Machine:\t%s\n", hostname);
  fprintf(OutputFile, "# Coefficients:\t%s\n", COEFF_ID);
  fprintf(OutputFile, "# Input file:\t%s\n", InputFileName);
  fprintf(OutputFile, "# Start time:\t%s", timestring);
  fprintf(OutputFile, "# Class:\t%d\n", UpToClass);
  fprintf(OutputFile, "# Flags:\t'%s'\n\n", flags);

  InitPcPres(Pres);

  TimeStamp("initialization");
  
  for (Class = 1; UpToClass == 0 || Class <= UpToClass; Class++) {
    unsigned OldNrPcGens = NrPcGens;

    if (Class >= 2) {
      if (Graded) GradedAddGen(); else AddGen(Pres);
    }

    InitStack();

    if (Class >= 2) {
      if (Graded) GradedTails(); else Tails();
    }
    
    InitMatrix();

    if (Class >= 2) {
      if (Graded) GradedConsistency(); else Consistency();
    }
    
    EvalAllRel(Pres);

    gpvec *rels;
    unsigned numrels;
    HermiteNormalForm(&rels, &numrels);
    
    unsigned trivialgens = ReducedPcPres(Pres, rels, numrels);

    FreeMatrix();
    FreeStack();

    NrCenGens -= trivialgens;
    NrTotalGens -= trivialgens;

    if (NrCenGens == 0)
      break;

    ExtendPcPres();

    fprintf(OutputFile, "# The %d%s factor has %d generators of relative orders ", Class, (Class % 10 == 1 && Class != 11) ? "st" : (Class % 10 == 2 && Class != 12) ? "st" : (Class % 10 == 3 && Class != 13) ? "rd" : "th", LastGen[Class]-LastGen[Class-1]);
    for (unsigned i = OldNrPcGens + 1; i <= NrPcGens; i++) {
      coeff_out_str(OutputFile, Exponent[i]);
      fprintf(OutputFile, i == NrPcGens ? "\n" : ", ");
    }
  }

  InitStack();
  PrintPcPres(Pres);
  FreeStack();

  TimeStamp("main()");

  FreePcPres(Pres);
  FreePresentation(Pres);

  return 0;
}
