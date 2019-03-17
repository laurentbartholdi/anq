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
static int Column;          /* Current character number. */
static int TColumn;         /* Character number where token starts. */
static const char *InFileName; /* Current input file name. */
static FILE *InFp;        /* Current input file pointer. */
static coeff N;           /* Contains the integer just read. */
static std::string GenName; /* Contains the generator name. */

void FreeNode(node *n) {
  switch (n->type) {
  case TGEN:
    break;
  case TNUM:
    clear(n->n);
    break;
  default:
    if (is_unary(n->type))
      FreeNode(n->u);
    else {
      FreeNode(n->l);
      FreeNode(n->r);
    }
  }
  delete n;
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
        return LASTGEN;
      return (gen) i;
    }
  }
  if (status == NOCREATE)
    return LASTGEN;

  pres.NrGens++;
  pres.Weight.resize(pres.NrGens + 1);
  pres.Weight[pres.NrGens] = weight;
  pres.GeneratorName.resize(pres.NrGens + 1);
  pres.GeneratorName[pres.NrGens].assign(GenName);
  
  return pres.NrGens;
}

static void SyntaxError(const char *format, ...) __attribute__((format(__printf__, 1, 2),noreturn));
static void SyntaxError(const char *format, ...) {
  va_list va;
  va_start (va, format);
  vfprintf(stderr, format, va);
  fprintf(stderr, " in file %s, line %d, char %d\n", InFileName, TLine, TColumn);
  exit(3);
}

static void ReadCh() {
  if ((Ch = getc(InFp)) == EOF)
    SyntaxError("I ran out of characters to read");
  Column++;
  if (Ch == '\\') {
    if ((Ch = getc(InFp)) == EOF)
      SyntaxError("I ran out of characters to read");
    if (Ch == '\n') {
      Line++;
      Column = 0;
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
      Column = 0;
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
  TColumn = Column;
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
      SyntaxError("Illegal character '%c' after ':'", Ch);
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
    zero(N);
    int base = (Ch == '0' ? coeff::characteristic : 10);
    
    while (isalnum(Ch)) {
      mul_si(N, N, base);
      add_si(N, N, isdigit(Ch) ? Ch - '0' : Ch + 10 - (isupper(Ch) ? 'A' : 'a'));
      ReadCh();
    }
    if (sign)
      neg(N, N);
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
      SyntaxError("Illegal character '%c' (ASCII %d) while parsing name", Ch, Ch);

    break;
  }
  }
}

node *Term(fppresentation &pres) {
  node *Expression(fppresentation&, int);
  
  if (is_unary(Token)) {
    node *n = new node{unary_node(Token)};
    int new_precedence = unary_prec(Token);
    NextToken();
    node *u = Expression(pres, new_precedence);
    if (u->type == TNUM) { /* compile-time evaluation */
      init(n->n);
      switch (n->type) {
      case TNEG:
	neg(n->n, u->n);
	break;
      case TINV:
	inv(n->n, u->n);
	break;
      default:
	abortprintf(3, "I can't evaluate a numerical expression with unary operator %s", nodename[n->type]);
      }
      n->type = TNUM;
      FreeNode(u);
    } else
      n->u = u;
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
      n = new node{oper, n, Expression(pres, 0)};
    }
    if (Token != close)
      SyntaxError("'%c' expected", closechar);
    NextToken();
    return n;
  }
  if (Token == NUMBER) {
    node *n = new node{TNUM, N};
    NextToken();
    return n;
  }
  if (Token == GEN) {
    const gen g = GenNumber(pres, NOCREATE, 0);
    if (g == LASTGEN)
      SyntaxError("Unkown generator %s", GenName.c_str());
    node *n = new node{TGEN, g};
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

#if defined(LIEALG) && defined(prime)
    if (oper == TPOW && u->type == TNUM) { // p-power mapping
      if (!cmp_si(u->n, prime)) {
	FreeNode(u);
	t = new node{TFROB, t};
	continue;
      } else
	abortprintf(3, "I can only accept p-power mapping with exponent %d", prime);
    }
#endif
    if (t->type == TNUM && u->type == TNUM) { // compile-time evaluation
      switch (oper) {
      case TPROD:
	mul(t->n, t->n, u->n);
	break;
      case TPOW:
	pow(t->n, t->n, u->n);
	break;
      case TSUM:
	add(t->n, t->n, u->n);
	break;
      case TDIFF:
	sub(t->n, t->n, u->n);
	break;
      default:
	abortprintf(3, "I can't evaluate a numerical expression with binary operator %d", oper);
      }
      FreeNode(u);
    } else
      t = new node{oper, t, u};
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
    if (n->g >= g)
      SyntaxError("Generator of rank <= %d expected, not %d", g, n->g);
    break;
#ifdef LIEALG
  case TPROD:
    if (n->l->type != TNUM)
      SyntaxError("LHS of TPROD should be number, not %s", nodename[n->l->type]);
    ValidateExpression(n->r, g);
    break;
#endif
#ifdef GROUP
  case TPOW: // conjugation or power
    ValidateExpression(n->l, g);
    if (n->r->type != TNUM)
      ValidateExpression(n->r, g);
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
    ValidateExpression(n->l, g);
    ValidateExpression(n->r, g);
    break;
#ifdef LIEALG // unary
  case TNEG:
  case TFROB:
#else
  case TINV:
#endif
    ValidateExpression(n->u, g);
    break;
  default:
    SyntaxError("Invalid operator %s in %s expression", nodename[n->type], LIEGPSTRING);
  }
}

void ValidateMap(const node *n, const fppresentation &pres, std::vector<bool> &seen) {
  if (n->type != TMAP)
    SyntaxError("Entries in {} should be arrows gen->expr");
  node *v = n->l;
  if (v->type != TGEN)
    SyntaxError("LHS of -> should be generator");
  if (seen[v->g])
    SyntaxError("Generator %s specified twice", pres.GeneratorName[v->g].c_str());
  ValidateExpression(n->r, LASTGEN);
  seen[v->g] = true;
}

fppresentation::fppresentation(const char *InputFileName) {
  if (InputFileName == nullptr) {
    InFileName = "<stdin>";
    InFp = stdin;
  } else {
    InFileName = InputFileName;
    InFp = fopen(InputFileName, "r");
    if (InFp == NULL)
      abortprintf(1, "Can't open input file '%s'", InputFileName);
  }

  NrGens = 0;
  
  Ch = '\0';
  Column = 0;
  Line = 1;
  init(N);
  
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
    gen g = GenNumber(*this, CREATE, weight);
    if (g == LASTGEN)
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
    node *n = Expression(*this, 0);

    if (n->type == TDRELR) /* switch sides */
      *n = node{TDREL, n->r, n->l};

    if (n->type == TREL) { /* chains of equalities */
      node *t;
      for (t = n; t->type == TREL; t = t->l)
	ValidateExpression(t->r, LASTGEN);
      ValidateExpression(t, LASTGEN);
    } else if (n->type == TDREL) {
      if (n->l->type != TGEN)
	SyntaxError("LHS should be generator, not %s", nodename[n->l->type]);

      for (const auto &m : Aliases)
	if (m->l->g == n->l->g)
	  SyntaxError("(At least) two definitions for generator %s", GeneratorName[n->l->g].c_str());
      
      ValidateExpression(n->r, n->l->g);
    } else if (n->type == TBRACE || n->type == TMAP) {
      std::vector<bool> seen(NrGens+1,false);
      node *t;
      for (t = n; t->type == TBRACE; t = t->l)
	ValidateMap(t->r, *this, seen);
      ValidateMap(t, *this, seen);

      for (const auto &n : Aliases)
	seen[n->l->g] = true; // don't force aliases to be defined

      for (unsigned i = 1; i <= NrGens; i++)
	if (!seen[i])
	  SyntaxError("Map doesn't specify image of generator %s", GeneratorName[i].c_str());
    } else
      ValidateExpression(n, LASTGEN);

    switch (n->type) {
    case TDREL:
      Aliases.push_back(n);
      break;
    case TBRACE: case TMAP:
      Endomorphisms.push_back(n);
      break;
    default:
      Relators.push_back(n);
    }
    
    if (Token == COMMA)
      NextToken();
    else
      break;
  }

  if (Token != RANGLE)
    SyntaxError("'>' expected");

  if (InputFileName != nullptr)
    fclose(InFp);

  if (Debug >= 2) {
    fprintf(LogFile, "# generators:");
    for (unsigned i = 1; i <= NrGens; i++)
      fprintf(LogFile, " %s", GeneratorName[i].c_str());
    fprintf(LogFile, "\n# aliases:");
    for (const auto &n : Aliases) {
      fprintf(LogFile, "\n#\t");
      printnode(LogFile, n);
    }
    fprintf(LogFile, "\n# relators:");
    for (const auto &n : Relators) {
      fprintf(LogFile, "\n#\t");
      printnode(LogFile, n);
    }
    fprintf(LogFile, "\n# endomorphisms:");
    for (const auto &n : Endomorphisms) {
      fprintf(LogFile, "\n#\t");
      printnode(LogFile, n);
    }
    fprintf(LogFile, "\n");
  }
  
  clear(N);
}

fppresentation::~fppresentation() {
  for (const auto &n : Relators)
    FreeNode(n);
  for (const auto &n : Aliases)
    FreeNode(n);
  for (const auto &n : Endomorphisms)
    FreeNode(n);
}

void fppresentation::printnodes(FILE *f, const node *n, nodetype t) const {
  if (n->type == t) {
    printnodes(f, n->l, t);
    fprintf(f, ",");
    n = n->r;
  }
  printnode(f, n);
}

void fppresentation::printnode(FILE *f, const node *n) const {
  switch (n->type) {
  case TNUM:
    fprintf(f, PRIcoeff, &n->n);
    break;
  case TGEN:
    fprintf(f, "%s", GeneratorName[n->g].c_str());
    break;
  case TNEG:
    fprintf(f, "-(");
    printnode(f, n->u);
    fprintf(f, ")");
    break;
  case TINV:
    fprintf(f, "~(");
    printnode(f, n->u);
    fprintf(f, ")");
    break;
#ifdef prime
  case TFROB:
    fprintf(f, "(");
    printnode(f, n->u);
    fprintf(f, ")^%d", prime);
    break;
#endif
  case TSUM:
    printnode(f, n->l);
    fprintf(f, " + ");
    printnode(f, n->r);
    break;
  case TDIFF:
    printnode(f, n->l);
    fprintf(f, " - ");
    printnode(f, n->r);
    break;
  case TPROD:
    fprintf(f, "(");
    printnode(f, n->l);
    fprintf(f, ")*(");
    printnode(f, n->r);
    fprintf(f, ")");
    break;
  case TQUO:
    fprintf(f, "(");
    printnode(f, n->l);
    fprintf(f, ")/(");
    printnode(f, n->r);
    fprintf(f, ")");
    break;
  case TLQUO:
    fprintf(f, "(");
    printnode(f, n->l);
    fprintf(f, ")\\(");
    printnode(f, n->r);
    fprintf(f, ")");
    break;
  case TPOW:
    fprintf(f, "(");
    printnode(f, n->l);
    fprintf(f, ")^(");
    printnode(f, n->r);
    fprintf(f, ")");
    break;
  case TBRACK:
    fprintf(f, "[");
    printnodes(f, n, TBRACK);
    fprintf(f, "]");
    break;
  case TBRACE:
    fprintf(f, "{");
    printnodes(f, n, TBRACE);
    fprintf(f, "}");
    break;
  case TMAP:
    printnode(f, n->l);
    fprintf(f, "→");
    printnode(f, n->r);
    break;
  case TREL:
    printnode(f, n->l);
    fprintf(f, " = ");
    printnode(f, n->r);
    break;
  case TDREL:
    printnode(f, n->l);
    fprintf(f, " := ");
    printnode(f, n->r);
    break;
  case TDRELR:
    printnode(f, n->l);
    fprintf(f, " =: ");
    printnode(f, n->r);
    break;
  default:
    abortprintf(3, "printnode: Illegal node of type %s", nodename[n->type]);
  }
}
