/******************************************************************************
**
**               Nilpotent Quotient for Lie Rings
** readpres.c                                                   Csaba Schneider
**                                                           schcs@math.klte.hu
*/

#include "lienq.h"
#include "readpres.h"
#include <string.h>
#include <ctype.h>
#include <stdio.h>

#define TRUE 1
#define FALSE 0

static char **Generators;

/* This fuction copies str1 to str2. */
static void CpStr(char *str1, char *str2)

{
  int i = 0;
  while ((str2[i] = str1[i]) != '\0')
    i++;
}

/* We need a function to compare two arbitrary strings. */
static bool CmpStr(char *str1, char *str2)

{
  int i = 0;
  while (str1[i] == str2[i] && str1[i] != '\0' && str2[i] != '\0')
    i++;
  if ((str1[i] == str2[i]) == '\0')
    return (TRUE);
  else
    return (FALSE);
}

void FreeNode(node *n)

{
  if (n->type != TGEN && n->type != TNUM) {
    FreeNode(n->cont.op.l);
    FreeNode(n->cont.op.r);
  }
  free(n);
}

static node *NewNode(int type)

{
  node *n;
  n = (node *) malloc(sizeof(node));
  n->type = type;
  return n;
}

#define NOCREATE 0
#define CREATE 1

static gen GenNumber(char *gname, int status)

{
  unsigned i;
  if (status == CREATE && NrGens == 0)
    Pres.Generators = (char **)malloc(2 * sizeof(char *));
  for (i = 1; i <= NrGens; i++) {
    if (!CmpStr(gname, Pres.Generators[i])) {
      if (status == CREATE)
        return (gen)0;
      return (gen)i;
    }
  }
  if (status == NOCREATE)
    return (gen)0;
  NrGens++;
  Pres.Generators = (char **)realloc(Pres.Generators, (NrGens + 1) * sizeof(char *));
  i = strlen(gname);
  Pres.Generators[NrGens] = (char *)malloc((i + 1) * sizeof(char));
  CpStr(gname, Pres.Generators[NrGens]);

  return NrGens;
}

char *GenName(gen g)

{
  if (g > NrGens)
    return ((char *)NULL);
  return Generators[g];
}

static void SyntaxError(const char *str)

{
  fprintf(stderr, "%s, line %d, char %d: %s.\n", InFileName, TLine, TChar, str);
  exit(1);
}

static void ReadCh() {
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

static void SkipBlanks() {
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

static void Number() {

  long long n = 0;

  while (isdigit(Ch)) {
    n = 10 * n + (Ch - '0');
    ReadCh();
  }

  N = n;
}

static void Generator() {

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

static void NextToken() {
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
      SyntaxError("illegal character");
  }
}

static void InitParser() {
  InFp = InputFile;
  InFileName = InputFileName;

  Ch = '\0';
  Char = 0;
  Line = 1;

  NextToken();
}

static node *SNumber() {

  node *n;

  if (Token == NUMBER) {
    n = NewNode(TNUM);
    n->cont.n = N;
    NextToken();
  } else if (Token == PLUS) {
    NextToken();
    if (Token != NUMBER)
      SyntaxError("Number expected");
    n = NewNode(TNUM);
    n->cont.n = N;
    NextToken();
  } else if (Token == MINUS) {
    NextToken();
    if (Token != NUMBER)
      SyntaxError("Number expected");
    n = NewNode(TNUM);
    n->cont.n = -N;
    NextToken();
  } else {
    SyntaxError("Number expected");
    n = NULL;
  }

  return n;
}

static node *LieProduct() {

  node *n, *o;
  extern node *Elem();

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

static node *Atom() {

  node *n;
  extern node *Elem();

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

static node *ModProduct() {

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
node *Elem() {

  node *n, *o;

  if (Token == PLUS || Token == MINUS || Token == NUMBER)
    o = ModProduct();
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
      o->cont.op.r = ModProduct();
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
static node *Relation() {

  node *n, *o;

  if (Token != GEN && Token != LPAREN && Token != LBRACK && Token != NUMBER)
    SyntaxError("relation expected");

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

static node **RelList() {

  node **rellist;
  unsigned n = 0;

  rellist = (node **) malloc(sizeof(node *));
  rellist[0] = (node *)NULL;
  if (Token != GEN && Token != LPAREN && Token != LBRACK && Token != NUMBER)

    return rellist;

  rellist = (node **) realloc((void *)rellist, 2 * sizeof(node *));
  rellist[n++] = Relation();
  while (Token == COMMA) {
    NextToken();
    rellist = (node **) realloc((void *)rellist, (n + 2) * sizeof(node *));
    rellist[n++] = Relation();
  }
  rellist[n] = (node *)0;

  return rellist;
}

/*
**    GenList() reads a list of generators. The defining rules are:
**
**    genlist:         generator | genseq
**    genseq:          'empty' | generator ',' genseq
*/
static int GenList() {

  if (Token != GEN) {
    perror("Do calculate by yourself your presentation without generators!");
    exit(2);
  }

  if (GenNumber(Gen, CREATE) == (gen)0)
    fprintf(stderr, "Warning: Duplicate generator: %s\n", Gen);
  NextToken();
  while (Token == COMMA) {
    NextToken();
    if (Token != GEN)
      SyntaxError("Generator expected");
    if (GenNumber(Gen, CREATE) == (gen)0)
      fprintf(stderr, "Warning: Duplicate generator: %s\n", Gen);
    NextToken();
  }

  return NrGens;
}

void ReadPresentation() {
  InitParser();

  if (Token != LANGLE)
    SyntaxError("presentation expected");
  NextToken();

  if (Token != GEN)
    SyntaxError("generator expected");

  Pres.NrGens = GenList();

  if (Token != PIPE)
    SyntaxError("vertical bar expected");
  NextToken();

  Pres.Relators = RelList();
  Pres.NrRels = 0;
  while (Pres.Relators[Pres.NrRels])
    Pres.NrRels++;
  if (Token != RANGLE)
    SyntaxError("presentation has to be closed by '>'");
}

void FreePresentation(void) {
  for (unsigned i = 1; i <= Pres.NrGens; i++)
    free(Pres.Generators[i]);
  free(Pres.Generators);
  for (unsigned i = 0; i < Pres.NrRels; i++)
    FreeNode(Pres.Relators[i]);
  free(Pres.Relators);
}

void PrintNode(node *n) {
  if (n->type == TNUM)
    fprintf(OutputFile, "%ld  ", n->cont.n.data);
  if (n->type == TGEN)
    fprintf(OutputFile, "%s  ", Generators[n->cont.g]);
  switch (n->type) {
  case TSUM: {
    PrintNode(n->cont.op.l);
    PrintNode(n->cont.op.r);
    fprintf(OutputFile, "+  ");
    break;
  }
  case TMPROD: {
    PrintNode(n->cont.op.l);
    PrintNode(n->cont.op.r);
    fprintf(OutputFile, "*  ");
    break;
  }
  case TLPROD: {
    PrintNode(n->cont.op.l);
    PrintNode(n->cont.op.r);
    fprintf(OutputFile, "[]  ");
    break;
  }
  case TREL: {
    PrintNode(n->cont.op.l);
    PrintNode(n->cont.op.r);
    fprintf(OutputFile, "=  ");
    break;
  }
  case TDRELL: {
    PrintNode(n->cont.op.l);
    PrintNode(n->cont.op.r);
    fprintf(OutputFile, ":=  ");
    break;
  }
  case TDRELR: {
    PrintNode(n->cont.op.l);
    PrintNode(n->cont.op.r);
    fprintf(OutputFile, "=:  ");
    break;
  }
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
    vl = NewGpVec(NrTotalGens);
    vr = NewGpVec(NrTotalGens);
    EvalRel(vl, rel->cont.op.l);
    EvalRel(vr, rel->cont.op.r);
    Sum(v, vl, vr);
    free(vl);
    free(vr);
    break;
  case TMPROD:
    EvalRel(v, rel->cont.op.r);
    ModProd((rel->cont.op.l)->cont.n, v);
    break;
  case TLPROD:
    vl = NewGpVec(NrTotalGens);
    vr = NewGpVec(NrTotalGens);
    EvalRel(vl, rel->cont.op.l);
    EvalRel(vr, rel->cont.op.r);
    Prod(v, vl, vr);
    free(vl);
    free(vr);
    break;
  case TGEN:
    CpVec(v, Epim(rel->cont.g));
    break;
  case TREL:
  case TDRELL:
  case TDRELR:
    vl = NewGpVec(NrTotalGens);
    vr = NewGpVec(NrTotalGens);
    EvalRel(vl, rel->cont.op.l);
    EvalRel(vr, rel->cont.op.r);
    Sum(v, vl, -1, vr);
    free(vl);
    free(vr);
    break;
  default:
    perror("Shouldn't happen");
    exit(2);
  }
}
