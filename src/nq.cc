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

// for debugging, lldb is lost when printing these objects
void PRINT(hollowpcvec &v) {
  printf(PRIhollowpcvec "\n", &v);
}

void PRINT(sparsepcvec &v) {
  printf(PRIsparsepcvec "\n", &v);
}

void PRINT(pccoeff &c) {
  printf(PRIpccoeff "\n", &c);
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

const char USAGE[] = "Usage: nq <options> [<inputfile>] [<maximal weight>]\n"
  "(with no input file, presentation is read from STDIN)\n"
  "\t[-A]\tprint GAP output, default false (load then object with `ReadAsFunction(filename)()`"
#ifdef GROUP
  ". once=PcpGroup, twice=PcGroup"
#endif
  "\n"
  "\t[-C]\ttoggle printing compact form of multiplication table, default true\n"
  "\t[-D]\tincrease debug level\n"
  "\t[-F <outputfile>]\n"
#ifdef LIEALG
  "\t[-G]\tcompute graded Lie algebra, default false\n"
#endif
#if defined(LIEALG) && PCCOEFF_P > 0 && PCCOEFF_K == 1
  "\t[-J]\tcompute Jacobson-restricted Lie algebra, default false\n"
#endif
#if defined(GROUP) && PCCOEFF_P > 0
  "\t[-J]\tcompute quotient by Jennings series, default false\n"
#endif
  "\t[-L <logfile>]\n"
  "\t[-M]\tcompute metabelian " LIEGPSTRING ", default false\n"
  "\t[-N <nilpotency class>]\n"
#if PCCOEFF_P == 0
    "\t[-T]\tforce successive quotients to be torsion-free, default false\n"
#endif
  "\t[-P]\ttoggle printing definitions of basic commutators, default false\n"
  "\t[-W <maximal weight>] (can also appear as last argument)\n"
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
template <typename T> static int coeff_print(void *ref)
{
  T *data = (T *) trio_get_argument(ref);
  if (data == nullptr)
    return -1;
  char *buffer = (char *) get_str(nullptr, 10, *data);
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
  for (const auto &kc : *data) {
    char *buffer = (char *) get_str(nullptr, 10, kc.second);
#ifdef GROUP
    if (first) first = false; else trio_print_string(ref, " * ");
    trio_print_string(ref, "a");
    trio_print_int(ref, kc.first);
    trio_print_string(ref, "^");
    trio_print_string(ref, buffer);
#else
    if (first) first = false; else trio_print_string(ref, " + ");
    trio_print_string(ref, buffer);
    trio_print_string(ref, "*a");
    trio_print_int(ref, kc.first);
#endif
    free(buffer);
  }
  return 0;
}  
#endif

char *utoa(char *s, unsigned n) {
  if (n == -1u)
    strcpy(s, "∞");
  else
    sprintf(s, "%u", n);
  return s;
}

int main(int argc, char **argv) {
  int c;
  bool PrintZeros = true, PrintCompact = true, PrintDefs = false;
  bool Graded = false, Metabelian = false, TorsionFree = false;
  int PrintGap = 0;
#ifdef LIEALG
  bool Jacobson = false;
  #else
  bool Jennings = false;
  const bool Jacobson = false;
#endif
  unsigned MaxWeight = -1u, NilpotencyClass = -1u;
  const char *InputFileName;

  // install handler
#ifndef NO_TRIO
  auto handle_pccoeff = trio_register(coeff_print<pccoeff>, "c%p"); // coeffs can be printed as PRIpccoeff
  auto handle_sparsepcvec = trio_register(cvec_print<sparsepcvec>, "s%p"); // sparsepcvecs can be printed as PRIsparsepcvec
  auto handle_sparsematvec = trio_register(cvec_print<sparsematvec>, "m%p"); // sparsematvecs can be printed as PRIsparsematvec
  auto handle_hollowpcvec = trio_register(cvec_print<hollowpcvec>, "h%p"); // hollowpcvecs can be printed as PRIhollowpcvec
#endif
  
  while ((c = getopt (argc, argv, "ACDF:GhJL:MN:PTW:Z")) != -1)
    switch (c) {
    case 'A':
      PrintGap++;
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
#ifdef LIEALG
    case 'G':
      Graded = true;
      break;
#endif
    case 'h':
      printf("%s\n\n%s", USAGE, EXTENDEDUSAGE);
      return 0;
#if defined(LIEALG) && PCCOEFF_P > 0 && PCCOEFF_K == 1
    case 'J':
      Jacobson = true;
      break;
#endif
#if defined(GROUP) && PCCOEFF_P > 0
    case 'J':
      Jennings = true;
      break;
#endif
#if PCCOEFF_P == 0
    case 'T':
      TorsionFree = true;
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

    fprintf(LogFile, "# The %s nilpotent quotient program, by Laurent Bartholdi (from Wernel Nickel and Csaba Schneider code)\n", LIEGPSTRING);
    fprintf(LogFile, "# Version %s, coefficients [pc=%s, mat=%s]\n", VERSION, pccoeff::COEFF_ID(), matcoeff::COEFF_ID());
    fprintf(LogFile, "# \"%s\" with input \"%s\" started %s on %s\n", argv[0], InputFileName ? InputFileName : "<stdin>", timestring, hostname);
    fprintf(LogFile, "# %s%s output %s%swill go to \"%s\"\n", PrintCompact ? "compact " : "", PrintGap ? "GAP" : "NQ", PrintZeros ? "with zeros " : "", PrintDefs ? "with defs" : "", OutputFile == stdout ? "<stdout>" : "file");

    char flags[1000] = "", nstring[20], mstring[20];
    if (Metabelian)
      strcat(flags, "metabelian, ");
#ifdef LIEALG
    if (Jacobson)
      strcat(flags, "Jacobson-restricted, ");
#else
    if (Jennings)
      strcat(flags, "Jennings, ");
#endif
    if (TorsionFree)
      strcat(flags, "torsion-free, ");
    if (Graded)
      strcat(flags, "graded, ");
    if (strlen(flags))
      flags[strlen(flags)-2] = 0; // remove ", "
    else
      strcat(flags, "none");
    fprintf(LogFile, "# flags %s; nilpotency class %s; maximal weight %s\n\n", flags, utoa(nstring, NilpotencyClass), utoa(mstring, MaxWeight));
  }
  
  fppresentation fppres(InputFileName, Jacobson);
    
#ifdef MEMCHECK
  mtrace();
#endif

  pcpresentation pc(fppres);
  pc.Graded = Graded;
  pc.Metabelian = Metabelian;
#ifdef LIEALG
  pc.Jacobson = Jacobson;
#else
  pc.Jennings = Jennings;
#endif
  pc.TorsionFree = TorsionFree;
  pc.NilpotencyClass = NilpotencyClass;

  for (pc.Class = 1; pc.Class <= MaxWeight; pc.Class++) {
    unsigned oldnrpcgens = pc.NrPcGens;

    unsigned nrcentralgens = pc.addtails(); // add fresh tails

    {
      matrix m(nrcentralgens, pc.NrPcGens+1, TorsionFree);
      
      pc.consistency(m); // enforce Jacobi and Z-linearity, via queue

      m.flushqueue();
      
      pc.evalrels(m);

      m.hermite();
    
      pc.reduce(m); // quotient the cover by rels
    }
    
    int newgens = pc.NrPcGens-oldnrpcgens;
    fprintf(LogFile, "# The %d%s factor has %d generator%s", pc.Class, ordinal(pc.Class), newgens, plural(newgens));
    if (newgens) {
      fprintf(LogFile, " of relative order%s ", plural(newgens));
      for (unsigned i = oldnrpcgens + 1; i <= pc.NrPcGens; i++) {
	if (pc.Exponent[i].z_p())
	  fprintf(LogFile, "∞");
	else
	  fprintf(LogFile, PRIpccoeff, &pc.Exponent[i]);
	if (i < pc.NrPcGens)
	  fprintf(LogFile, ", ");
      }
    }
    fprintf(LogFile,"\n");

    if (MaxWeight == -1u && newgens == 0)
      break;
  }

  if (PrintGap > 0)
    pc.printGAP(OutputFile, PrintGap);  
  else
    pc.print(OutputFile, PrintCompact, PrintDefs, PrintZeros);

  TimeStamp("main()");

#ifndef NO_TRIO
  trio_unregister(handle_hollowpcvec);
  trio_unregister(handle_sparsematvec);
  trio_unregister(handle_sparsepcvec);
  trio_unregister(handle_pccoeff);
#endif
  
  return 0;
}
