/******************************************************************************
**
**               Nilpotent Quotient for Lie Rings
** readpres.c                                                   Csaba Schneider
**                                                           schcs@math.klte.hu
*/

#include "lienq.h"
#include <string.h>
#include <ctype.h>
#include <stdio.h>

#if 0
static const char *TokenName[] = {
  "LParen", "RParen", "LBrack", "RBrack",  "LBrace",  "RBrace",
  "Mult",   "Power",  "Equal",  "DEqualL", "DEqualR", "Plus",
  "Minus",  "LAngle", "RAngle", "Pipe",    "Comma",   "Number",
  "Gen"};
#endif

enum token {
  LPAREN, RPAREN, LBRACK, RBRACK, LBRACE, RBRACE,
  MULT, POWER, EQUAL, DEQUALL, DEQUALR, PLUS,
  MINUS, LANGLE, RANGLE, PIPE, COMMA, SEMICOLON, NUMBER,
  GEN };
  
static char Ch;           /* Contains the next char on the input. */
static token Token;       /* Contains the current token. */
static int Line;          /* Current line number. */
static int TLine;         /* Line number where token starts. */
static int Char;          /* Current character number. */
static int TChar;         /* Character number where token starts. */
static const char *InFileName;  /* Current input file name. */
static FILE *InFp;        /* Current input file pointer. */
static coeff N;           /* Contains the integer just read. */
static char Gen[128];     /* Contains the generator name. */

/* The following structure will carry the presentation given by the user. */

presentation Pres;

void FreeNode(node *n) {
  if (n->type != TGEN && n->type != TNUM) {
    FreeNode(n->cont.op.l);
    FreeNode(n->cont.op.r);
  }
  delete n;
}

static node *NewNode(nodetype type) {
  node *n = new node;
  n->type = type;
  return n;
}

enum genstatus { NOCREATE, CREATE };

static gen GenNumber(char *gname, genstatus status) {
  if (status == CREATE && Pres.NrGens == 0)
    Pres.Generators = (char **) malloc(2 * sizeof(char *));
  for (unsigned i = 1; i <= Pres.NrGens; i++) {
    if (!strcmp(gname, Pres.Generators[i])) {
      if (status == CREATE)
        return (gen) 0;
      return (gen) i;
    }
  }
  if (status == NOCREATE)
    return (gen) 0;
  Pres.NrGens++;
  Pres.Generators = (char **) realloc(Pres.Generators, (Pres.NrGens + 1) * sizeof(char *));
  Pres.Generators[Pres.NrGens] = new char[strlen(gname) + 1];
  strcpy(Pres.Generators[Pres.NrGens], gname);

  return Pres.NrGens;
}

char *GenName(gen g) {
  if (g > Pres.NrGens)
    return (char *) NULL;
  return Pres.Generators[g];
}

static void SyntaxError(const char *str) {
  fprintf(stderr, "%s, line %d, char %d: %s.\n", InFileName, TLine, TChar, str);
  exit(1);
}

static void ReadCh(void) {
  Ch = getc(InFp);
  Char++;
  if (Ch == '\\') {
    Ch = getc(InFp);
    if (Ch == '\n') {
      Line++;
      Char = 0;
      ReadCh();
    } else {
      ungetc(Ch, InFp);
      Ch = '\\';
    }
  }
}

static void SkipBlanks(void) {
  if (Ch == '\0')
    ReadCh();
  while (Ch == ' ' || Ch == '\t' || Ch == '\n' || Ch == '#') {
    if (Ch == '#')
      while (Ch != '\n')
        ReadCh();
    if (Ch == '\n') {
      Line++;
      Char = 0;
    }
    ReadCh();
  }
}

static void Number(void) {
  coeff_set_si(N, 0);

  while (isdigit(Ch)) {
    coeff_mul_si(N, N, 10);
    coeff_add_si(N, N, Ch - '0');
    ReadCh();
  }
}

static void Generator(void) {
  int i;

  for (i = 0; i < 127 && (isalnum(Ch) || Ch == '_' || Ch == '.'); i++) {
    Gen[i] = Ch;
    ReadCh();
  }
  Gen[i] = '\0';
  /* Discard the rest. */
  while (isalnum(Ch) || Ch == '_' || Ch == '.')
    ReadCh();
}

static void NextToken(void) {
  SkipBlanks();
  TChar = Char;
  TLine = Line;
  switch (Ch) {
  case '(': {
    Token = LPAREN;
    ReadCh();
    break;
  }
  case ')': {
    Token = RPAREN;
    ReadCh();
    break;
  }
  case '[': {
    Token = LBRACK;
    ReadCh();
    break;
  }
  case ']': {
    Token = RBRACK;
    ReadCh();
    break;
  }
  case '{': {
    Token = LBRACE;
    ReadCh();
    break;
  }
  case '}': {
    Token = RBRACE;
    ReadCh();
    break;
  }

  case '*': {
    Token = MULT;
    ReadCh();
    break;
  }
  case '^': {
    Token = POWER;
    ReadCh();
    break;
  }
  case ':': {
    ReadCh();
    if (Ch != '=')
      SyntaxError("illegal character");
    Token = DEQUALL;
    ReadCh();
    break;
  }
  case '=': {
    ReadCh();
    if (Ch != ':')
      Token = EQUAL;
    else {
      Token = DEQUALR;
      ReadCh();
    }
    break;
  }

  case '+': {
    Token = PLUS;
    ReadCh();
    break;
  }
  case '-': {
    Token = MINUS;
    ReadCh();
    break;
  }

  case '<': {
    Token = LANGLE;
    ReadCh();
    break;
  }
  case '>': {
    Token = RANGLE;
    ReadCh();
    break;
  }

  case '|': {
    Token = PIPE;
    ReadCh();
    break;
  }
  case ',': {
    Token = COMMA;
    ReadCh();
    break;
  }
  case ';': {
    Token = SEMICOLON;
    ReadCh();
    break;
  }

  case '0':
  case '1':
  case '2':
  case '3':
  case '4':
  case '5':
  case '6':
  case '7':
  case '8':
  case '9': {
    Token = NUMBER;
    Number();
    break;
  }
  default:
    if (isalnum(Ch) || Ch == '_' || Ch == '.') {
      Token = GEN;
      Generator();
      break;
    } else
      SyntaxError("Illegal character");
  }
}

static void InitParser(const char *InputFileName) {
  InFp = fopen(InputFileName, "r");
  if (InFp == NULL)
    SyntaxError("Can't open input file");
  InFileName = InputFileName;

  Ch = '\0';
  Char = 0;
  Line = 1;

  coeff_init(N);
  
  NextToken();
}

static void CloseParser(void) {
  fclose(InFp);
}

static node *SNumber(void) {
  node *n;

  if (Token == NUMBER) {
    n = NewNode(TNUM);
    coeff_init_set(n->cont.n, N);
    NextToken();
  } else if (Token == PLUS) {
    NextToken();
    if (Token != NUMBER)
      SyntaxError("Number expected");
    n = NewNode(TNUM);
    coeff_init_set(n->cont.n, N);
    NextToken();
  } else if (Token == MINUS) {
    NextToken();
    if (Token != NUMBER)
      SyntaxError("Number expected");
    n = NewNode(TNUM);
    coeff_init(n->cont.n);
    coeff_neg(n->cont.n, N);
    NextToken();
  } else {
    SyntaxError("Number expected");
    n = NULL;
  }

  return n;
}

static node *LieProduct(void) {
  node *n, *o;
  extern node *Elem(void);

  if (Token != LBRACK)
    SyntaxError("Left square bracket expected");

  NextToken();
  if (Token != GEN && Token != LPAREN && Token != LBRACK)
    SyntaxError("Word expected");

  o = Elem();
  if (Token != COMMA)
    SyntaxError("Comma expected");
  while (Token == COMMA) {
    NextToken();
    if (Token != GEN && Token != LPAREN && Token != LBRACK)
      SyntaxError("Word expected");
    n = NewNode(TLPROD);
    n->cont.op.l = o;
    n->cont.op.r = Elem();
    o = n;
  }
  if (Token != RBRACK)
    SyntaxError("Right square bracket missing");
  NextToken();
  return n;
}

static node *Atom(void) {
  node *n;
  extern node *Elem(void);

  if (Token == GEN) {
    n = NewNode(TGEN);
    n->cont.g = GenNumber(Gen, NOCREATE);
    if (n->cont.g == (gen)0)
      SyntaxError("Unkown generator");
    NextToken();
  } else if (Token == LPAREN) {
    NextToken();
    n = Elem();
    if (Token != RPAREN)
      SyntaxError("Closing parenthesis expected");
    NextToken();
  } else if (Token == LBRACK) {
    n = LieProduct();
  } else {
    SyntaxError("Generator, left parenthesis or commutator expected");
    n = NULL;
  }
  return n;
}

static node *ModuleProduct(void) {
  node *n, *o;

  if (Token != PLUS && Token != MINUS && Token != NUMBER)
    SyntaxError("Integer expected in module-operation");
  o = SNumber();

  if (Token == MULT) {
    NextToken();
    if (Token != GEN && Token != LPAREN && Token != NUMBER && Token != LBRACK)
      SyntaxError("Something is wrong in module operation");

    n = o;
    o = NewNode(TMPROD);
    o->cont.op.l = n;
    o->cont.op.r = Atom();
  }
  return o;
}

/*
**    Elem() reads a Lie-algebra element. The defining rule is:
**
**    element:      module-product | module-product '+' element
**
**    A word starts either with 'generator', with '(', with '['
**    or with integer number (ring-element).
*/
node *Elem(void) {
  node *n, *o;

  if (Token == PLUS || Token == MINUS || Token == NUMBER)
    o = ModuleProduct();
  else if (Token == GEN || Token == LPAREN || Token == LBRACK)
    o = Atom();
  else
    SyntaxError("Error in Sum");
  while (Token == PLUS) {
    NextToken();
    n = o;
    o = NewNode(TSUM);
    o->cont.op.l = n;
    if (Token == NUMBER || Token == PLUS || Token == MINUS)
      o->cont.op.r = ModuleProduct();
    else if (Token == GEN || Token == LPAREN || Token == LBRACK)
      o->cont.op.r = Atom();
    else
      SyntaxError("Error in Sum");
  }

  return o;
}

/*
**    Relation() reads a relation. The defining rule is:
**
**    relation:        element | element '=' element | element '=:' element |
**    element ':=' element
**
**    A relation starts either with 'generator', with '(', with '[' or
**    with integer (ring-element).
*/
static node *Relation(void) {
  node *n, *o;

  if (Token != GEN && Token != LPAREN && Token != LBRACK && Token != NUMBER)
    SyntaxError("Relation expected");

  o = Elem();
  if (Token == EQUAL) {
    NextToken();
    n = o;
    o = NewNode(TREL);
    o->cont.op.l = n;
    o->cont.op.r = Elem();
  } else if (Token == DEQUALL) {
    NextToken();
    n = o;
    o = NewNode(TDRELL);
    o->cont.op.l = n;
    o->cont.op.r = Elem();
  } else if (Token == DEQUALR) {
    NextToken();
    n = o;
    o = NewNode(TDRELR);
    o->cont.op.l = n;
    o->cont.op.r = Elem();
  }

  return o;
}

/*
**    RelList() reads a list of relations. The defining rules are:
**
**    rellist:         'empty' | relseq
**    relseq:          relation | relation ',' relseq
**
**    A relation starts either with 'generator', with '(', with '['
**    or with an integer (ring-element).
*/

static int RelList(node **&rellist) {
  unsigned n = 0;

  rellist = (node **) malloc(sizeof(node *));
  if (Token == GEN || Token == LPAREN || Token == LBRACK || Token == NUMBER) {
    rellist = (node **) realloc(rellist, 2 * sizeof(node *));
    rellist[n++] = Relation();
    while (Token == COMMA) {
      NextToken();
      rellist = (node **) realloc(rellist, (n + 2) * sizeof(node *));
      rellist[n++] = Relation();
    }
  }
  return n;
}

/*
**    GenList() reads a list of generators. The defining rules are:
**
**    genlist:         generator | genseq
**    genseq:          'empty' | generator ',' genseq
*/
static void GenList() {
  for (;;) {
    if (Token != GEN)
      SyntaxError("Generator expected");
    
    if (GenNumber(Gen, CREATE) == (gen) 0) {
      char s[1000];
      sprintf(s, "Duplicate generator: %s", Gen);
      SyntaxError(s);
    }
    NextToken();

    if (Token != COMMA) break;

    NextToken();
  }
}

void ReadPresentation(const char *InputFileName) {
  InitParser(InputFileName);
  Pres.NrGens = 0;
  
  if (Token != LANGLE)
    SyntaxError("Presentation expected");
  NextToken();

  if (Token != GEN)
    SyntaxError("Generator expected");

  GenList();

  if (Token != PIPE)
    SyntaxError("Vertical bar expected");
  NextToken();

  Pres.NrRels = RelList(Pres.Relators);

  if (Token == PIPE) {
    NextToken();
    Pres.NrExtraRels = RelList(Pres.ExtraRelators);
  } else
    Pres.NrExtraRels = 0, Pres.ExtraRelators = NULL;

  if (Token != RANGLE)
    SyntaxError("Presentation has to be closed by '>'");

  CloseParser();
}

void FreePresentation(void) {
  for (unsigned i = 1; i <= Pres.NrGens; i++)
    free(Pres.Generators[i]);
  free(Pres.Generators);
  for (unsigned i = 0; i < Pres.NrRels; i++)
    FreeNode(Pres.Relators[i]);
  free(Pres.Relators);
  if (Pres.ExtraRelators != NULL) {
    for (unsigned i = 0; i < Pres.NrExtraRels; i++)
      FreeNode(Pres.ExtraRelators[i]);
    free(Pres.ExtraRelators);
  }
}

void PrintNode(node *n) {
  switch (n->type) {
  case TNUM:
    fprintf(OutputFile, "%ld  ", coeff_get_si(n->cont.n));
    break;
  case TGEN:
    fprintf(OutputFile, "%s  ", Pres.Generators[n->cont.g]);
    break;
  case TSUM:
    PrintNode(n->cont.op.l);
    PrintNode(n->cont.op.r);
    fprintf(OutputFile, "+  ");
    break;
  case TMPROD:
    PrintNode(n->cont.op.l);
    PrintNode(n->cont.op.r);
    fprintf(OutputFile, "*  ");
    break;
  case TLPROD:
    PrintNode(n->cont.op.l);
    PrintNode(n->cont.op.r);
    fprintf(OutputFile, "[]  ");
    break;
  case TREL:
    PrintNode(n->cont.op.l);
    PrintNode(n->cont.op.r);
    fprintf(OutputFile, "=  ");
    break;
  case TDRELL:
    PrintNode(n->cont.op.l);
    PrintNode(n->cont.op.r);
    fprintf(OutputFile, ":=  ");
    break;
  case TDRELR:
    PrintNode(n->cont.op.l);
    PrintNode(n->cont.op.r);
    fprintf(OutputFile, "=:  ");
    break;
  }
}

/*
** We have to enforce the relations of the finite presentation in the PC
** presentation. It means, the relations among the generators of the finite
** presentation will hold among their epimorphic images as well.
** The result of this task will be a linear equation system over the integers
** which can be considered as power relations between the polycyclic
** generators.
*/

void EvalRel(gpvec v, node *rel) {
  gpvec vl, vr;
  switch (rel->type) {
  case TSUM:
    vl = FreshVec();
    vr = FreshVec();
    EvalRel(vl, rel->cont.op.l);
    EvalRel(vr, rel->cont.op.r);
    Sum(v, vl, vr);
    PopVec();
    PopVec();
    break;
  case TMPROD:
    EvalRel(v, rel->cont.op.r);
    Prod(v, (rel->cont.op.l)->cont.n, v);
    break;
  case TLPROD:
    vl = FreshVec();
    vr = FreshVec();
    EvalRel(vl, rel->cont.op.l);
    EvalRel(vr, rel->cont.op.r);
    Prod(v, vl, vr);
    PopVec();
    PopVec();
    break;
  case TGEN:
    Copy(v, Epim(rel->cont.g));
    break;
  case TREL:
  case TDRELL:
  case TDRELR:
    vl = FreshVec();
    vr = FreshVec();
    EvalRel(vl, rel->cont.op.l);
    EvalRel(vr, rel->cont.op.r);
    Diff(v, vl, vr);
    PopVec();
    PopVec();
    break;
  default:
    perror("Shouldn't happen");
    exit(2);
  }
}
