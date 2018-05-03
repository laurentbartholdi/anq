/******************************************************************************
**
**               Nilpotent Quotient for Lie Rings
** readpres.c                                                   Csaba Schneider
**                                                           schcs@math.klte.hu
*/

#include "lienq.h"
#include <ctype.h>
#include <stdio.h>
#include <stdarg.h>

enum token {
  LPAREN, RPAREN, LBRACK, RBRACK, LBRACE, RBRACE,
  NUMBER, GEN,
  MULT, DIV, POWER, PLUS, MINUS, INVERSE, EQUAL, DEQUALL, DEQUALR,
  LANGLE, RANGLE, PIPE, COMMA, SEMICOLON,
  BADTOKEN };

const char *nodename[] = {"TNUM", "TGEN", "TBRACK", "TBRACE", "TPROD", "TQUO",
			  "TPOW", "TSUM", "TDIFF", "TREL", "TDREL", "TDRELR",
			  "TNEG", "TINV"};

enum associativity {
  LEFTASSOC, RIGHTASSOC };

constexpr bool is_unary(token t) {
  return t == MINUS || t == INVERSE;
}
constexpr bool is_binary(token t) {
  return t >= MULT && t <= DEQUALR;
}
constexpr associativity token_assoc(token t) {
  return t == POWER ? RIGHTASSOC : LEFTASSOC;
					 }
constexpr int unary_prec(token t) {
  return t == INVERSE ? 6 : t == MINUS ? 4 : 0;
}
constexpr int binary_prec(token t) {
  return (t == MINUS || t == PLUS) ? 3 : (t == MULT || t == DIV) ? 5 : t == POWER ? 7 : 0;
}
constexpr bool is_relation(token t) {
  return t <= DEQUALR;
}
constexpr nodetype unary_node(token t) {
  return t == MINUS ? TNEG : t == INVERSE ? TINV : TINVALID;
}
constexpr nodetype binary_node(token t) {
  return t == MULT ? TPROD : t == DIV ? TQUO : t == POWER ? TPOW : t == PLUS ? TSUM : t == MINUS ? TDIFF : t == EQUAL ? TREL : t == DEQUALL ? TDREL : t == DEQUALR ? TDRELR : TINVALID;
}

static char Ch;           /* Contains the next char on the input. */
static token Token;       /* Contains the current token. */
static int Line;          /* Current line number. */
static int TLine;         /* Line number where token starts. */
static int Char;          /* Current character number. */
static int TChar;         /* Character number where token starts. */
static const char *InFileName; /* Current input file name. */
static FILE *InFp;        /* Current input file pointer. */
static coeff N;           /* Contains the integer just read. */
static std::string GenName; /* Contains the generator name. */

void FreeNode(node *n) {
  switch (n->type) {
  case TGEN:
    break;
  case TNUM:
    coeff_clear(n->cont.n);
    break;
  default:
    if (is_unary(n->type))
      FreeNode(n->cont.u);
    else {
      FreeNode(n->cont.bin.l);
      FreeNode(n->cont.bin.r);
    }
  }
  delete n;
}

static node *NewNode(nodetype type) {
  node *n = new node;
  n->type = type;
  return n;
}

enum genstatus { NOCREATE, CREATE };

static gen GenNumber(presentation &pres, genstatus status, unsigned weight) {
  if (status == CREATE && pres.NrGens == 0) {
    pres.Weight.resize(1); // we start indexing at 1
    pres.GeneratorName.resize(1);
  }
  for (unsigned i = 1; i <= pres.NrGens; i++) {
    if (GenName == pres.GeneratorName[i]) {
      if (status == CREATE)
        return (gen) 0;
      return (gen) i;
    }
  }
  if (status == NOCREATE)
    return (gen) 0;

  pres.NrGens++;
  pres.Weight.resize(pres.NrGens + 1);
  pres.Weight[pres.NrGens] = weight;
  pres.GeneratorName.resize(pres.NrGens + 1);
  pres.GeneratorName[pres.NrGens].assign(GenName);
  
  return pres.NrGens;
}

static void SyntaxError(const char *format, ...) __attribute__((format(printf, 1, 2),noreturn));
static void SyntaxError(const char *format, ...) {
  va_list va;
  va_start (va, format);
  vfprintf(stderr, format, va);
  fprintf(stderr, " in file %s, line %d, char %d\n", InFileName, TLine, TChar);
  exit(3);
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

/* gets a new token from the stream, and puts it in the global variable
   Token.
   Also sets the globals GenName and N in case a generator / number is read.
*/
static void NextToken(void) {
  SkipBlanks();
  TChar = Char;
  TLine = Line;
  Token = BADTOKEN;
  switch (Ch) {
  case '(':
    Token = LPAREN;
    ReadCh();
    break;
  
  case ')':
    Token = RPAREN;
    ReadCh();
    break;
  
  case '[':
    Token = LBRACK;
    ReadCh();
    break;
  
  case ']':
    Token = RBRACK;
    ReadCh();
    break;
  
  case '{':
    Token = LBRACE;
    ReadCh();
    break;
  
  case '}':
    Token = RBRACE;
    ReadCh();
    break;
  

  case '*':
    Token = MULT;
    ReadCh();
    break;
  
  case '/':
    Token = DIV;
    ReadCh();
    break;
  
  case '^':
    Token = POWER;
    ReadCh();
    break;
    
  case '+':
    Token = PLUS;
    ReadCh();
    break;
    
  case '-':
    Token = MINUS;
    ReadCh();
    break;
    
  case '~':
    Token = INVERSE;
    ReadCh();
    break;
  

  case ':':
    ReadCh();
    if (Ch != '=')
      SyntaxError("Illegal character '%c'", Ch);
    Token = DEQUALL;
    ReadCh();
    break;
  
  case '=':
    ReadCh();
    if (Ch != ':')
      Token = EQUAL;
    else {
      Token = DEQUALR;
      ReadCh();
    }
    break;
  
  case '<':
    Token = LANGLE;
    ReadCh();
    break;
  
  case '>':
    Token = RANGLE;
    ReadCh();
    break;
  
  case '|':
    Token = PIPE;
    ReadCh();
    break;
  
  case ',':
    Token = COMMA;
    ReadCh();
    break;
  
  case ';':
    Token = SEMICOLON;
    ReadCh();
    break;
  
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
    coeff_set_si(N, 0);
    int base = (Ch == '0' ? coeff_base : 10);
    
    while (isdigit(Ch)) {
      coeff_mul_si(N, N, base);
      coeff_add_si(N, N, Ch - '0');
      ReadCh();
    }
    break;
  }

  default: {
    Token = GEN;
    GenName.clear();

    while (isalnum(Ch) || Ch == '_' || Ch == '.') {
      GenName.push_back(Ch);
      ReadCh();
    }

    if (GenName.empty())
      SyntaxError("Illegal character '%c'", Ch);

    break;
  }
  }
}

node *Term(presentation &pres) {
  node *Expression(presentation&, int);
  
  if (is_unary(Token)) {
    node *n = NewNode(unary_node(Token));
    int new_precedence = unary_prec(Token);
    NextToken();
    node *u = Expression(pres, new_precedence);
    if (u->type == TNUM) { /* compile-time evaluation */
      coeff_init(n->cont.n);
      switch (n->type) {
      case TNEG:
	coeff_neg(n->cont.n, u->cont.n);
	break;
#if 0 /* not implemented */
      case TINV:
	coeff_inv(n->cont.n, u->cont.n);
	break;
#endif
      default:
	abortprintf(3, "I can't evaluate a numerical expression with unary operator %s", nodename[n->type]);
      }
      n->type = TNUM;
      FreeNode(u);
    } else
      n->cont.u = u;
    return n;
  }
  if (Token == LPAREN) {
    NextToken();
    node *n = Expression(pres, 0);
    if (Token != RPAREN)
      SyntaxError("')' expected");
    NextToken();
    return n;
  }
  if (Token == LBRACK || Token == LBRACE) {
    token close = (Token == LBRACK ? RBRACK : RBRACE);
    nodetype oper = (Token == LBRACK ? TBRACK : TBRACE);  
    char closechar = (Token == LBRACK ? ']' : '}');  
    NextToken();
    node *n = Expression(pres, 0);
    while (Token == COMMA) {
      NextToken();
      node *p = NewNode(oper);
      p->cont.bin.l = n;
      p->cont.bin.r = Expression(pres, 0);
      n = p;
    }
    if (Token != close)
      SyntaxError("'%c' expected", closechar);
    NextToken();
    return n;
  }
  if (Token == NUMBER) {
    node *n = NewNode(TNUM);
    coeff_init_set(n->cont.n, N);
    NextToken();
    return n;
  }
  if (Token == GEN) {
    node *n = NewNode(TGEN);
    if ((n->cont.g = GenNumber(pres, NOCREATE, 0)) == (gen) 0)
      SyntaxError("Unkown generator %s", GenName.c_str());
    NextToken();
    return n;
  }
  SyntaxError("Term expected");
}

node *Expression(presentation &pres, int precedence) {
  node *t = Term(pres);
  int new_precedence;
  
  while (is_binary(Token) && (new_precedence = binary_prec(Token)) >= precedence) {
    if (token_assoc(Token) == LEFTASSOC)
      new_precedence++;
    nodetype oper = binary_node(Token);
    NextToken();

    node *u = Expression(pres, new_precedence);

    if (t->type == TNUM && u->type == TNUM) { /* compile-time evaluation */
      switch (oper) {
      case TPROD:
	coeff_mul(t->cont.n, t->cont.n, u->cont.n);
	break;
      case TPOW:
	coeff_pow(t->cont.n, t->cont.n, u->cont.n);
	break;
      case TSUM:
	coeff_add(t->cont.n, t->cont.n, u->cont.n);
	break;
      case TDIFF:
	coeff_sub(t->cont.n, t->cont.n, u->cont.n);
	break;
      default:
	abortprintf(3, "I can't evaluate a numerical expression with binary operator %d", oper);
      }
      FreeNode(u);
    } else {
      node *n = NewNode(oper);
      n->cont.bin = {.l = t, .r = u};
      t = n;
    }
  }
  return t;
}

static void ValidateLieExpression(node *n, gen g) {
  /* check that n is a valid Lie expression, involving only generators of index < g.

     For TPROD, LHS must be a number, and all other terms must be Lie expressions.
     Forbid TINV, TQUO, TBRACE, TREL, TDREL.
  */

  switch (n->type) {
  case TNUM:
    SyntaxError("Lie expression expected, not number");
  case TGEN:
    if (n->cont.g >= g)
      SyntaxError("Generator of rank <= %d expected, not %d", g, n->cont.g);
    break;
  case TINV:
  case TQUO:
  case TBRACE:
  case TREL:
  case TDREL:
    SyntaxError("Operator %s unexpected", nodename[n->type]);
  case TPROD:
    if (n->cont.bin.l->type != TNUM)
      SyntaxError("LHS of TPROD should be number, not %s", nodename[n->cont.bin.l->type]);
    ValidateLieExpression(n->cont.bin.r, g);
    break;
  case TBRACK:
  case TSUM:
  case TDIFF:
    ValidateLieExpression(n->cont.bin.l, g);
    ValidateLieExpression(n->cont.bin.r, g);
    break;
  case TNEG:
    ValidateLieExpression(n->cont.u, g);
    break;
  default:
    SyntaxError("Invalid expression of type %s", nodename[n->type]);
  }
}

void ReadPresentation(presentation &pres, const char *InputFileName) {
  bool readstdin = (InputFileName[0] == '-' && InputFileName[1] == 0);
  
  if (readstdin)
    InFp = stdin;
  else
    InFp = fopen(InputFileName, "r");
  if (InFp == NULL)
    abortprintf(1, "Can't open input file '%s'", InputFileName);
  InFileName = InputFileName;

  pres.NrGens = 0;
  
  Ch = '\0';
  Char = 0;
  Line = 1;
  coeff_init(N);
  
  NextToken(); // start parsing

  if (Token == LANGLE)
    NextToken();
  else
    SyntaxError("'<' expected");

  unsigned weight = 1;

  /* get generators */
  while (true) {
    while (Token == SEMICOLON) {
      weight++;
      NextToken();
    }

  read_gen:
    if (Token != GEN)
      SyntaxError("Generator expected");
    gen g = GenNumber(pres, CREATE, weight);
    if (g == (gen) 0)
      SyntaxError("Duplicate generator %s", GenName.c_str());
    NextToken();

    if (Token == PIPE)
      break;

    if (Token == COMMA) {
      NextToken();
      goto read_gen;
    }
  }

  NextToken();

  /* get relators */
  while (is_relation(Token)) {
    node *n = Expression(pres, 0);

    if (n->type == TDRELR) { /* switch sides */
      n->type = TDREL;
      n->cont.bin = {.l = n->cont.bin.r, .r = n->cont.bin.l};
    }
    if (n->type == TREL) {
      ValidateLieExpression(n->cont.bin.l, EOW);
      ValidateLieExpression(n->cont.bin.r, EOW);
    } else if (n->type == TDREL) {
      if (n->cont.bin.l->type != TGEN)
	SyntaxError("LHS should be generator, not %s", nodename[n->cont.bin.l->type]);
      ValidateLieExpression(n->cont.bin.r, n->cont.bin.l->cont.g);
    } else
      ValidateLieExpression(n, EOW);

    if (n->type == TDREL)
      pres.Aliases.push_back(n);
    else
      pres.Relators.push_back(n);
    
    if (Token == COMMA)
      NextToken();
    else
      break;
  }

  /* get extra elements to evaluate in result */
  if (Token == PIPE) {
    NextToken();

    while (is_relation(Token)) {
      node *n = Expression(pres, 0);
      ValidateLieExpression(n, EOW);
      pres.Extra.push_back(n);
      if (Token == COMMA)
	NextToken();
      else
	break;
    }
  }

  if (Token != RANGLE)
    SyntaxError("'>' expected");

  if (!readstdin)
    fclose(InFp);

  coeff_clear(N);
}

void FreePresentation(presentation &Pres) {
  for (auto n : Pres.Relators)
    FreeNode(n);
  for (auto n : Pres.Aliases)
    FreeNode(n);
  for (auto n : Pres.Extra)
    FreeNode(n);
}

void PrintNode(FILE *f, const presentation &pres, node *n) {
  switch (n->type) {
  case TNUM:
    coeff_out_str(f, n->cont.n);
    break;
  case TGEN:
    fprintf(f, "%s", pres.GeneratorName[n->cont.g].c_str());
    break;
  case TNEG:
    fprintf(f, "-");
    PrintNode(f, pres, n->cont.u);
    break;
  case TINV:
    fprintf(f, "~");
    PrintNode(f, pres, n->cont.u);
    break;
  case TSUM:
    PrintNode(f, pres, n->cont.bin.l);
    fprintf(f, " + ");
    PrintNode(f, pres, n->cont.bin.r);
    break;
  case TDIFF:
    PrintNode(f, pres, n->cont.bin.l);
    fprintf(f, " - ");
    PrintNode(f, pres, n->cont.bin.r);
    break;
  case TPROD:
    PrintNode(f, pres, n->cont.bin.l);
    fprintf(f, "*");
    PrintNode(f, pres, n->cont.bin.r);
    break;
  case TQUO:
    PrintNode(f, pres, n->cont.bin.l);
    fprintf(f, "/");
    PrintNode(f, pres, n->cont.bin.r);
    break;
  case TPOW:
    PrintNode(f, pres, n->cont.bin.l);
    fprintf(f, "^");
    PrintNode(f, pres, n->cont.bin.r);
    break;
  case TBRACK:
    fprintf(f, "[");
    PrintNode(f, pres, n->cont.bin.l);
    fprintf(f, ",");
    PrintNode(f, pres, n->cont.bin.r);
    fprintf(f, "]");
    break;
  case TBRACE:
    fprintf(f, "{");
    PrintNode(f, pres, n->cont.bin.l);
    fprintf(f, ",");
    PrintNode(f, pres, n->cont.bin.r);
    fprintf(f, "}");
    break;
  case TREL:
    PrintNode(f, pres, n->cont.bin.l);
    fprintf(f, " = ");
    PrintNode(f, pres, n->cont.bin.r);
    break;
  case TDREL:
    PrintNode(f, pres, n->cont.bin.l);
    fprintf(f, " := ");
    PrintNode(f, pres, n->cont.bin.r);
    break;
  case TDRELR:
    PrintNode(f, pres, n->cont.bin.l);
    fprintf(f, " =: ");
    PrintNode(f, pres, n->cont.bin.r);
    break;
  default:
    abortprintf(3, "PrintNode: Illegal node of type %s", nodename[n->type]);
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

void EvalRel(const pcpresentation &pc, gpvec v, node *rel) {
  gpvec vl, vr;
  switch (rel->type) {
  case TSUM:
    vl = FreshVec();
    vr = FreshVec();
    EvalRel(pc, vl, rel->cont.bin.l);
    EvalRel(pc, vr, rel->cont.bin.r);
    Sum(v, vl, vr);
    PopVec();
    PopVec();
    break;
  case TPROD:
    EvalRel(pc, v, rel->cont.bin.r);
    Prod(v, rel->cont.bin.l->cont.n, v);
    break;
  case TBRACK:
    vl = FreshVec();
    vr = FreshVec();
    EvalRel(pc, vl, rel->cont.bin.l);
    EvalRel(pc, vr, rel->cont.bin.r);
    LieBracket(pc, v, vl, vr);
    PopVec();
    PopVec();
    break;
  case TGEN:
    Copy(v, pc.Epimorphism[rel->cont.g]);
    break;
  case TNEG:
    EvalRel(pc, v, rel->cont.u);
    Neg(v);
    break;
  case TDIFF:
  case TREL:
    vl = FreshVec();
    vr = FreshVec();
    EvalRel(pc, vl, rel->cont.bin.l);
    EvalRel(pc, vr, rel->cont.bin.r);
    Diff(v, vl, vr);
    PopVec();
    PopVec();
    break;
  default:
    abortprintf(3, "EvalRel: operator of type %s should not occur", nodename[rel->type]);
  }
}

/* evaluate all relations, and add them to the relation matrix */
void EvalAllRel(const pcpresentation &pc, const presentation &pres) {
  gpvec v = FreshVec();

  for (auto n : pres.Aliases) {
    gpvec temp = FreshVec();
    EvalRel(pc, temp, n->cont.bin.r);
    Collect(pc, v, temp);
    PopVec();
    if (Debug >= 2) {
      fprintf(LogFile, "# aliasing relation: ");
      PrintNode(LogFile, pres, n);
      fprintf(LogFile, " ("); PrintVec(LogFile, v); fprintf(LogFile, ")\n");
    }
    gen g = n->cont.bin.l->cont.g;
    pc.Epimorphism[g] = ResizeVec(pc.Epimorphism[g], Length(pc.Epimorphism[g]), Length(v));
    Copy(pc.Epimorphism[g], v);
  }
  
  for (auto n : pres.Relators) {
    gpvec temp = FreshVec();
    EvalRel(pc, temp, n);
    Collect(pc, v, temp);
    PopVec();
    if (Debug >= 2) {
      fprintf(LogFile, "# relation: ");
      PrintNode(LogFile, pres, n);
      fprintf(LogFile, " ("); PrintVec(LogFile, v); fprintf(LogFile, ")\n");
    }
    AddRow(v);
  }
  PopVec();
  
  TimeStamp("EvalAllRel()");
}
