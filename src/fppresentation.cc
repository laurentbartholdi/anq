/******************************************************************************
**
**               Nilpotent Quotient for Lie Rings
** readpres.c                                                   Csaba Schneider
**                                                           schcs@math.klte.hu
*/

#include "nq.h"
#include <ctype.h>
#include <stdio.h>
#include <stdarg.h>

enum token {
  LPAREN, RPAREN, LBRACK, RBRACK, LBRACE, RBRACE,
  NUMBER, GEN,
  MULT, DIV, LDIV, POWER, PLUS, MINUS, ARROW, EQUAL, DEQUALL, DEQUALR, INVERSE,
  LANGLE, RANGLE, PIPE, COMMA, SEMICOLON,
  BADTOKEN };

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
inline int unary_prec(token t) {
  switch (t) {
  case INVERSE: return 6;
  case MINUS: return 4;
  default: return 0;
  }
}
inline int binary_prec(token t) {
  switch (t) {
  case MINUS: case PLUS: return 3;
  case MULT: case DIV: case LDIV: return 5;
  case POWER: return 7;
  default: return 0;
  }
}
constexpr bool is_relation(token t) {
  return t <= DEQUALR;
}
const nodetype unary_node(token t) {
  switch (t) {
  case MINUS: return TNEG;
  case INVERSE: return TINV;
  default: return TINVALID;
  }
}
inline nodetype binary_node(token t) {
  switch (t) {
  case MULT: return TPROD;
  case DIV: return TQUO;
  case LDIV: return TLQUO;
  case POWER: return TPOW;
  case PLUS: return TSUM;
  case MINUS: return TDIFF;
  case EQUAL: return TREL;
  case DEQUALL: return TDREL;
  case DEQUALR: return TDRELR;
  case ARROW: return TMAP;
  default: return TINVALID;
  }
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

static gen GenNumber(fppresentation &pres, genstatus status, unsigned weight) {
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

/* gets a new token from the stream, and puts it in the global variable
   Token.
   Also sets the globals GenName and N in case a generator / number is read.
*/
static void NextToken() {
  SkipBlanks();
  TChar = Char;
  TLine = Line;
  Token = BADTOKEN;
  bool sign = false;
  
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
  
  case '\\':
    Token = LDIV;
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
  
  case '-':
    Token = MINUS;
    ReadCh();
    if (Ch == '>') {
      Token = ARROW;
      ReadCh();
      break;
    } else if (isdigit(Ch))
      sign = true;  // and fall through
    else
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
    
    while (isalnum(Ch)) {
      coeff_mul_si(N, N, base);
      coeff_add_si(N, N, isdigit(Ch) ? Ch - '0' : Ch + 10 - (isupper(Ch) ? 'A' : 'a'));
      ReadCh();
    }
    if (sign)
      coeff_neg(N, N);
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

node *Term(fppresentation &pres) {
  node *Expression(fppresentation&, int);
  
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
      case TINV:
	coeff_inv(n->cont.n, u->cont.n);
	break;
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
    const token close = (Token == LBRACK ? RBRACK : RBRACE);
    const nodetype oper = (Token == LBRACK ? TBRACK : TBRACE);  
    const char closechar = (Token == LBRACK ? ']' : '}');  
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

node *Expression(fppresentation &pres, int precedence) {
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

static void ValidateExpression(const node *n, gen g) {
  /* check that n is a valid expression, involving only generators of index < g.

     in Lie algebras: for TPROD, LHS must be a number, and all other
     terms must be Lie expressions.  Forbid TINV, TQUO, TLQUO, TREL, TDREL.

     in groups: forbid TSUM, TDIFF, TNEG, TREL, TDREL.
  */

  switch (n->type) {
  case TNUM:
    SyntaxError("Expected a %s expression, not a number", LIEGPSTRING);
  case TGEN:
    if (n->cont.g >= g)
      SyntaxError("Generator of rank <= %d expected, not %d", g, n->cont.g);
    break;
#ifdef LIEALG
  case TPROD:
    if (n->cont.bin.l->type != TNUM)
      SyntaxError("LHS of TPROD should be number, not %s", nodename[n->cont.bin.l->type]);
    ValidateExpression(n->cont.bin.r, g);
    break;
#endif
#ifdef GROUP
  case TPOW: // conjugation or power
    ValidateExpression(n->cont.bin.l, g);
    if (n->cont.bin.r->type != TNUM)
      ValidateExpression(n->cont.bin.r, g);
    break;
#endif
  case TBRACK: // binary
#ifdef LIEALG
  case TSUM:
  case TDIFF:
#else
  case TPROD:
  case TQUO:
  case TLQUO:
#endif    
    ValidateExpression(n->cont.bin.l, g);
    ValidateExpression(n->cont.bin.r, g);
    break;
#ifdef LIEALG // unary
  case TNEG:
#else
  case TINV:
#endif
    ValidateExpression(n->cont.u, g);
    break;
  case TMAP:
    SyntaxError("Maps must be enclosed in {}");    
  default:
    SyntaxError("Invalid operator %s in %s expression", nodename[n->type], LIEGPSTRING);
  }
}

void ValidateMap(const node *n, const fppresentation &pres, std::vector<bool> &seen) {
  if (n->type != TMAP)
    SyntaxError("Entries in {} should be arrows gen->expr");
  node *v = n->cont.bin.l;
  if (v->type != TGEN)
    SyntaxError("LHS of -> should be generator");
  if (seen[v->cont.g])
    SyntaxError("Generator %s specified twice", pres.GeneratorName[v->cont.g].c_str());
  seen[v->cont.g] = true;
}

void ReadPresentation(fppresentation &pres, const char *InputFileName) {
  bool readstdin = (InputFileName[0] == 0);
  
  if (readstdin)
    InFp = stdin;
  else {
    InFp = fopen(InputFileName, "r");
    if (InFp == NULL)
      abortprintf(1, "Can't open input file '%s'", InputFileName);
  }
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
      ValidateExpression(n->cont.bin.l, INFINITY);
      ValidateExpression(n->cont.bin.r, INFINITY);
    } else if (n->type == TDREL) {
      if (n->cont.bin.l->type != TGEN)
	SyntaxError("LHS should be generator, not %s", nodename[n->cont.bin.l->type]);
      ValidateExpression(n->cont.bin.r, n->cont.bin.l->cont.g);
    } else if (n->type == TBRACE || n->type == TMAP) {
      std::vector<bool> seen(pres.NrGens+1,false);
      node *t;
      for (t = n; t->type == TBRACE; t = t->cont.bin.r)
	ValidateMap(t->cont.bin.l, pres, seen);
      ValidateMap(t, pres, seen);
      for (unsigned i = 1; i <= pres.NrGens; i++)
	if (!seen[i])
	  SyntaxError("Map doesn't specify image of generator %s", pres.GeneratorName[i].c_str());
    } else
      ValidateExpression(n, INFINITY);

    if (n->type == TDREL)
      pres.Aliases.push_back(n);
    else if (n->type == TBRACE || n->type == TMAP)
      pres.Endomorphisms.push_back(n);
    else
      pres.Relators.push_back(n);
    
    if (Token == COMMA)
      NextToken();
    else
      break;
  }

  if (Token != RANGLE)
    SyntaxError("'>' expected");

  if (!readstdin)
    fclose(InFp);

  if (Debug >= 2) {
    fprintf(LogFile, "# generators:");
    for (unsigned i = 1; i <= pres.NrGens; i++)
      fprintf(LogFile, " %s", pres.GeneratorName[i].c_str());
    fprintf(LogFile, "\n# aliases:");
    for (auto n : pres.Aliases) {
      fprintf(LogFile, "\n#\t");
      PrintNode(LogFile, pres, n);
    }
    fprintf(LogFile, "\n# relators:");
    for (auto n : pres.Relators) {
      fprintf(LogFile, "\n#\t");
      PrintNode(LogFile, pres, n);
    }
    fprintf(LogFile, "\n# endomorphisms:");
    for (auto n : pres.Endomorphisms) {
      fprintf(LogFile, "\n#\t");
      PrintNode(LogFile, pres, n);
    }
    fprintf(LogFile, "\n");
  }
  
  coeff_clear(N);
}

void FreePresentation(fppresentation &pres) {
  for (auto n : pres.Relators)
    FreeNode(n);
  for (auto n : pres.Aliases)
    FreeNode(n);
  for (auto n : pres.Endomorphisms)
    FreeNode(n);
}

void PrintNode(FILE *f, const fppresentation &pres, node *n) {
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
  case TLQUO:
    PrintNode(f, pres, n->cont.bin.l);
    fprintf(f, "\\");
    PrintNode(f, pres, n->cont.bin.r);
    break;
  case TPOW:
    PrintNode(f, pres, n->cont.bin.l);
    fprintf(f, "^");
    PrintNode(f, pres, n->cont.bin.r);
    break;
  case TBRACK:
    fprintf(f, "[");
    while (n->type == TBRACK) {
      PrintNode(f, pres, n->cont.bin.l);
      fprintf(f, ",");
      n = n->cont.bin.r;
    }
    PrintNode(f, pres, n);
    fprintf(f, "]");
    break;
  case TBRACE:
    fprintf(f, "{");
    while (n->type == TBRACE) {
      PrintNode(f, pres, n->cont.bin.l);
      fprintf(f, ",");
      n = n->cont.bin.r;
    }
    PrintNode(f, pres, n);
    fprintf(f, "}");
    break;
  case TMAP:
    PrintNode(f, pres, n->cont.bin.l);
    fprintf(f, "→");
    PrintNode(f, pres, n->cont.bin.r);
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
