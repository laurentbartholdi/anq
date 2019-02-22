/******************************************************************************
**
**                 Nilpotent Quotient for Lie Rings
** nq.c                                                         Csaba Schneider
**                                                           schcs@math.klte.hu
*/

#include "nq.h"
#include <string.h>
#include <sys/types.h>
#include <unistd.h>
#ifdef MEMCHECK
#include <mcheck.h>
#endif

FILE *OutputFile = stdout, *LogFile = stdout;
unsigned Debug = 0;

#define S(x) #x
#define S_(x) S(x)
#define Scoeff_base S_(coeff_base)

const char USAGE[] = "Usage: nq <options> [<inputfile>] [<maximal weight>]\n"
  "(with no input file, presentation is read from STDIN)\n"
  "\t[-A]\ttoggle GAP output, default false (load then object with `ReadAsFunction(filename)()`)\n"
  "\t[-C]\ttoggle printing compact form of multiplication table, default true\n"
  "\t[-D]\tincrease debug level\n"
  "\t[-F <outputfile>]\n"
  "\t[-G]\tcompute graded Lie algebra, default false\n"
#if coeff_base != 10
  "\t[-J]\tcompute " Scoeff_base "-Jennings series, default false\n"
#endif
  "\t[-L <logfile>]\n"
  "\t[-M]\tcompute metabelian " LIEGPSTRING ", default false\n"
  "\t[-N <nilpotency class>]\n"
  "\t[-P]\ttoggle printing definitions of basic commutators, default false\n"
  "\t[-W <maximal weight>] (can also appear as last argument)\n"
  "\t[-X <exponent>]\tset exponent for p-central series, default 0\n"
  "\t[-Z]\ttoggle printing zeros in multiplication table, default true";

const char EXTENDEDUSAGE[] = "Presentation format:\n"
  "\tpresentation = '<' (';'* gen (',' gen)*)* '|' exprlist? '>'\n"
  "(each ';' in presentation increases weight, starting from 1.)\n"
  "(second exprlist gives relations. third exprlist is evaluated in quotient)\n"
  "\tgen = '[a-zA-Z_.]' '[a-zA-Z0-9_.]'*\n"
  "\texprlist = expr (',' expr)*\n"
  "\texpr = term | term ('*' | '/' | '^' | '+' | '-' | '=' | ':=' | '=:') term\n"
  "\tterm = '-' expr | '~' expr | '(' expr ')' | '[' exprlist ']' | '{' exprlist '}' | number | gen (with usual precedence)\n"
  "\tnumber = [0-9]+ (if starting with 0 then in given base, otherwise base 10)\n";

#ifndef NO_TRIO
static int coeff_print(void *ref)
{
  coeff *data = (coeff *) trio_get_argument(ref);
  if (data == nullptr)
    return -1;
  char *buffer = coeff_get_str(nullptr, 10, *data);
  trio_print_string(ref, buffer);
  int len = strlen(buffer);
  free(buffer);
  return len;
}  

template <typename V> static int cvec_print(void *ref)
{
  V *data = (V *) trio_get_argument(ref);
  if (data == nullptr)
    return -1;

  bool first = true;
  for (auto kc : *data) {
    char *buffer = coeff_get_str(nullptr, 10, kc.second);
#ifdef LIEALG
    if (first) first = false; else trio_print_string(ref, " + ");
    trio_print_string(ref, buffer);
    trio_print_string(ref, "*a");
    trio_print_int(ref, kc.first);
#else
    if (first) first = false; else trio_print_string(ref, " * ");
    trio_print_string(ref, "a");
    trio_print_int(ref, kc.first);
    trio_print_string(ref, "^");
    trio_print_string(ref, buffer);
#endif
    free(buffer);
  }
  return 0;
}  
#endif

char *utoa(char *s, unsigned n) {
  if (n == INFINITY)
    strcpy(s, "∞");
  else
    sprintf(s, "%u", n);
  return s;
}

int main(int argc, char **argv) {
  int c;
  bool PrintZeros = true, PrintCompact = true, PrintDefs = false, Gap = false, Graded = false, PAlgebra = false, Metabelian = false, Jennings = false;
  coeff TorsionExp;
  coeff_init_set_si(TorsionExp, 0);
  unsigned MaxWeight = INFINITY, NilpotencyClass = INFINITY;
  const char *InputFileName;

  // install handler
#ifndef NO_TRIO
  trio_register(coeff_print, "c%p"); // coeffs can be printed as PRIcoeff
  trio_register(cvec_print<sparsecvec>, "s%p"); // sparsecvecs can be printed as PRIsparsecvec
  trio_register(cvec_print<hollowcvec>, "h%p"); // hollowcvecs can be printed as PRIhollowcvec
#endif

  while ((c = getopt (argc, argv, "ACDF:GhJL:MN:PX:W:Z")) != -1)
    switch (c) {
    case 'A':
      Gap ^= true;
      break;
    case 'C':
      PrintCompact ^= true;
      break;
    case 'D':
      Debug++;
      break;
    case 'F':
      OutputFile = fopen(optarg, "w");
      if (OutputFile == NULL)
	abortprintf(1, "I can't open output file '%s'", optarg);
      break;
    case 'G':
      Graded = true;
      break;
    case 'h':
      printf("%s\n\n%s", USAGE, EXTENDEDUSAGE);
      return 0;
#if coeff_base != 10
    case 'J':
      Jennings = true;
      PAlgebra = true;
      coeff_set_si(TorsionExp, coeff_base);
      break;
#endif
    case 'L':
      LogFile = fopen(optarg, "w");
      if (LogFile == NULL)
	abortprintf(1, "I can't open log file '%s'", optarg);
      break;
    case 'M':
      Metabelian = true;
      break;
    case 'N':
      NilpotencyClass = atoi(optarg);
      break;
    case 'P':
      PrintDefs ^= true;
      break;
    case 'X':
      PAlgebra = true;
      coeff_set_str(TorsionExp, optarg, 10);
      break;
    case 'W':
      MaxWeight = atoi(optarg);
      break;
    case 'Z':
      PrintZeros ^= true;
      break;
    default:
      abortprintf(1, "Undefined flag '%c'\n%s", c, USAGE);
    }
  
  if (optind < argc)
    InputFileName = argv[optind++];
  else
    InputFileName = nullptr;

  if (optind < argc)
    MaxWeight = atoi(argv[optind++]);

  if (optind != argc)
    abortprintf(1, "I need at most two arguments, as input filename and maximal weight\n%s", USAGE);

  {
    char hostname[128];
    gethostname(hostname, 128);

    time_t t = time((time_t *) 0);
    char timestring[128];
    strftime(timestring, 128, "%c", localtime(&t));

    fprintf(LogFile, "# The %s nilpotent quotient program, by Csaba Schneider & Laurent Bartholdi\n", LIEGPSTRING);
    fprintf(LogFile, "# Version %s, coefficients %s\n", VERSION, COEFF_ID);
    fprintf(LogFile, "# \"%s\" with input \"%s\" started %s on %s\n", argv[0], InputFileName ? InputFileName : "<stdin>", timestring, hostname);
    fprintf(LogFile, "# %s%s output %s%swill go to \"%s\"\n", PrintCompact ? "compact " : "", Gap ? "GAP" : "NQ", PrintZeros ? "with zeros " : "", PrintDefs ? "with defs" : "", OutputFile == stdout ? "<stdout>" : "file");

    char flags[1000] = "", nstring[20], mstring[20];
    if (Metabelian)
      strcat(flags, "metabelian, ");
    if (Jennings)
      strcat(flags, "Jennings, ");
    if (Graded)
      strcat(flags, "graded, ");
    if (PAlgebra)
      sprintf(flags+strlen(flags), "exponent-" PRIcoeff ", ", &TorsionExp);
    if (strlen(flags))
      flags[strlen(flags)-2] = 0; // remove ", "
    else
      strcat(flags, "none");
    fprintf(LogFile, "# flags %s; nilpotency class %s; maximal weight %s\n\n", flags, utoa(nstring, NilpotencyClass), utoa(mstring, MaxWeight));
  }
  
  fppresentation fppres;
  ReadPresentation(fppres, InputFileName);
    
#ifdef MEMCHECK
  mtrace();
#endif

  pcpresentation pc;  
  InitPcPres(pc, fppres);
  pc.Graded = Graded;
  pc.PAlgebra = PAlgebra;
  pc.Metabelian = Metabelian;
  pc.Jennings = Jennings;
  pc.NilpotencyClass = NilpotencyClass;
  coeff_set(pc.TorsionExp, TorsionExp);

  for (pc.Class = 1; pc.Class <= MaxWeight; pc.Class++) {
    unsigned oldnrpcgens = pc.NrPcGens;

    unsigned nrcentralgens = AddTails(pc, fppres); // add fresh tails

    InitMatrix(pc.PAlgebra ? &pc.TorsionExp : nullptr, pc.NrPcGens+1, nrcentralgens);

    Consistency(pc); // enforce Jacobi and Z-linearity, via queue

    FlushMatrixQueue();

    EvalAllRel(pc, fppres); // evaluate relations

    sparsecmat rels = GetMatrix();
    
    ReducePcPres(pc, fppres, rels); // quotient the cover by rels

    FreeMatrix();

    int newgens = pc.NrPcGens-oldnrpcgens;
    fprintf(LogFile, "# The %d%s factor has %d generator%s", pc.Class, ordinal(pc.Class), newgens, plural(newgens));
    if (newgens) {
      fprintf(LogFile, " of relative order%s ", plural(newgens));
      for (unsigned i = oldnrpcgens + 1; i <= pc.NrPcGens; i++)
	fprintf(LogFile, PRIcoeff "%s", &pc.Exponent[i], i == pc.NrPcGens ? "" : ", ");
    }
    fprintf(LogFile,"\n");

    if (MaxWeight == INFINITY && newgens == 0)
      break;
  }

  if (Gap)
    PrintGAPPres(OutputFile, pc, fppres);  
  else
    PrintPcPres(OutputFile, pc, fppres, PrintCompact, PrintDefs, PrintZeros);

  TimeStamp("main()");

  FreePcPres(pc, fppres);
  FreePresentation(fppres);
  coeff_clear(TorsionExp);
  
  return 0;
}
