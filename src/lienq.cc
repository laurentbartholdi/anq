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

const char USAGE[] = "Usage: lienq [-G] [-D] [-A] [-Z] [-P] [-F <outputfile>] <inputfile> [<class>]";

bool PrintZeros = false, Graded = false, Gap = false, PrintDefs = false;
unsigned Debug = 0;
unsigned Class;

int main(int argc, char **argv) {
  unsigned UpToClass = -1;
  char flags[24] = "";
  int c;
  
  while ((c = getopt (argc, argv, "GDAZF:P")) != -1)
    switch (c) {
    case 'G':
      Graded = !Graded;
      strcat(flags, "-G ");
      break;
    case 'D':
      Debug++;
      strcat(flags, "-D ");
      break;
    case 'A':
      Gap = !Gap;
      strcat(flags, "-A ");
      break;
    case 'F':
      OutputFile = fopen(optarg, "w");
      if (OutputFile == NULL)
	abortprintf(1, "I can't open the output file '%s'", optarg);
      strcat(flags, "-F ");
      break;
    case 'Z':
      PrintZeros = !PrintZeros;
      strcat(flags, "-Z ");
      break;
    case 'P':
      PrintDefs = !PrintDefs;
      strcat(flags, "-P ");
      break;
    default:
      abortprintf(1, "Undefined flag '%c'\n%s", c, USAGE);
    }
  
  if (optind >= argc)
    abortprintf(1, "I need at least one name as input file\n%s", USAGE);

  char *InputFileName = argv[optind++];
  ReadPresentation(InputFileName);
  
  if (optind < argc)
    UpToClass = atoi(argv[optind]);

  char hostname[128];
  char timestring[26];
  time_t t = time((time_t *) 0);
  strcpy(timestring, ctime(&t));
  
  gethostname(hostname, 128);
  fprintf(OutputFile, "# The Lie algebra Nilpotent Quotient Program\n"
	  "# for calculating nilpotent quotients in finitely presented Lie rings by Csaba Schneider.\n");
  fprintf(OutputFile, "# Program:    %s, version %s\n", argv[0], VERSION);
  fprintf(OutputFile, "# Machine:    %s\n", hostname);
  fprintf(OutputFile, "# Input file: %s\n", InputFileName);
  fprintf(OutputFile, "# Time:       %s", timestring);
  fprintf(OutputFile, "# Class:      %d\n", UpToClass);
  fprintf(OutputFile, "# Flags:      %s\n\n", flags);

  InitPcPres();
  InitEpim();

  TimeStamp("initialization");
  
  for (Class = 1; UpToClass == 0 || Class <= UpToClass; Class++) {
    unsigned OldNrPcGens = NrPcGens;

    if (Class >= 2) {
      if (Graded) GradedAddGen(); else AddGen();
    }

    InitStack();

    if (Class >= 2) {
      if (Graded) GradedTails(); else Tails();
    }
    
    InitMatrix();

    if (Class >= 2) {
      if (Graded) GradedConsistency(); else Consistency();
    }
    
    EvalAllRel();

    HermiteNormalForm();
    
    unsigned trivialgens = ReducedPcPres();

    FreeMatrix();
    FreeStack();

    NrCenGens -= trivialgens;
    NrTotalGens -= trivialgens;

    if (NrCenGens == 0)
      break;

    ExtendPcPres();

    fprintf(OutputFile, "# The %d%s factor has %d generators of relative orders ", Class, (Class % 10 == 1 && Class != 11) ? "st" : (Class % 10 == 2 && Class != 12) ? "st" : (Class % 10 == 3 && Class != 13) ? "rd" : "th", LastGen[Class]-LastGen[Class-1]);
    for (unsigned i = OldNrPcGens + 1; i <= NrPcGens; i++)
      fprintf(OutputFile, "%ld%s", coeff_get_si(Exponent[i]), i == NrPcGens ? "\n" : ", ");
  }

  InitStack();
  PrintPcPres();
  FreeStack();

  TimeStamp("main()");

  FreePresentation();
  FreeEpim();
  FreePcPres();

  return 0;
}