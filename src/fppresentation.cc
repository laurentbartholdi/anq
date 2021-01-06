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

const gen LASTGEN = -1u;

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
  return !(t >= LANGLE);
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

static token Token;	/* Contains the current token. */
static int Line;	/* Current line number. */
static int TLine;	/* Line number where token starts. */
static int Column;	/* Current character number. */
static int TColumn;	/* Character number where token starts. */
static std::string CurLine; /* Current line, for debugging */
static const char *InFileName; /* Current input file name. */
static FILE *InFp;	/* Current input file pointer. */
static fpcoeff N;	/* Contains the integer just read. */
static std::string GenName; /* Contains the generator name. */

static void SyntaxError(const char *format, ...) __attribute__((format(__printf__, 1, 2),noreturn));
static void SyntaxError(const char *format, ...) {
  va_list va;
  va_start (va, format);
  vfprintf(stderr, format, va);
  fprintf(stderr, " in file %s, line %d, char %d\n%s\n%*s", InFileName, TLine, TColumn, CurLine.c_str(), TColumn, "^");
  exit(3);
}

void FreeNode(node *n) {
  switch (n->type) {
  case TGEN:
    break;
  case TNUM:
    n->n.clear();
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

static gen GetGen(fppresentation &pres) {
  // we start at 0, including the name "p" at position 0, to recognize p-powers
  for (unsigned i = 0; i <= pres.NrGens; i++) {
    if (GenName == pres.GeneratorName[i])
      return (gen) i;
  }
  SyntaxError("Unkown generator %s", GenName.c_str());
}

static char ReadCh() {
  char Ch;

  if ((Ch = getc(InFp)) == EOF)
    SyntaxError("I ran out of characters to read");
  Column++;
  CurLine.push_back(Ch);
  if (Ch == '\\') {
    if ((Ch = getc(InFp)) == EOF)
      SyntaxError("I ran out of characters to read");
    if (Ch == '\n') {
      Line++;
      Column = 0;
      CurLine = "";
      ReadCh();
    } else {
      ungetc(Ch, InFp);
      Ch = '\\';
    }
  }

  return Ch;
}

/* gets a new token from the stream, and puts it in the global variable
   Token.
   Also sets the globals GenName and N in case a generator / number is read.
*/
static void NextToken() {
  static char Ch = '\0';
  
  /* skip blanks */
  if (Ch == '\0')
    Ch = ReadCh();
  while (Ch == ' ' || Ch == '\t' || Ch == '\n' || Ch == '#') {
    if (Ch == '#')
      while (Ch != '\n')
        Ch = ReadCh();
    if (Ch == '\n') {
      Line++;
      Column = 0;
      CurLine = "";
    }
    Ch = ReadCh();
  }

  TColumn = Column;
  TLine = Line;
  Token = BADTOKEN;
  
  switch (Ch) {
  case '(':
    Token = LPAREN;
    Ch = '\0';
    break;
  
  case ')':
    Token = RPAREN;
    Ch = '\0';
    break;
  
  case '[':
    Token = LBRACK;
    Ch = '\0';
    break;
  
  case ']':
    Token = RBRACK;
    Ch = '\0';
    break;
  
  case '{':
    Token = LBRACE;
    Ch = '\0';
    break;
  
  case '}':
    Token = RBRACE;
    Ch = '\0';
    break;
  

  case '*':
    Token = MULT;
    Ch = '\0';
    break;
  
  case '/':
    Token = DIV;
    Ch = '\0';
    break;
  
  case '\\':
    Token = LDIV;
    Ch = '\0';
    break;
  
  case '^':
    Token = POWER;
    Ch = '\0';
    break;
    
  case '+':
    Token = PLUS;
    Ch = '\0';
    break;
    
  case '~':
    Token = INVERSE;
    Ch = '\0';
    break;
  

  case ':':
    Ch = ReadCh();
    if (Ch != '=')
      SyntaxError("Illegal character '%c' after ':'", Ch);
    Token = DEQUALL;
    Ch = '\0';
    break;
  
  case '=':
    Ch = ReadCh();
    if (Ch != ':')
      Token = EQUAL;
    else {
      Token = DEQUALR;
      Ch = '\0';
    }
    break;
  
  case '<':
    Token = LANGLE;
    Ch = '\0';
    break;
  
  case '>':
    Token = RANGLE;
    Ch = '\0';
    break;
  
  case '|':
    Token = PIPE;
    Ch = '\0';
    break;
  
  case ',':
    Token = COMMA;
    Ch = '\0';
    break;
  
  case ';':
    Token = SEMICOLON;
    Ch = '\0';
    break;
  
  case '-':
    Token = MINUS;
    Ch = ReadCh();
    if (Ch == '>') {
      Token = ARROW;
      Ch = '\0';
    }
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
    int base = (Ch == '0' ? fpcoeff::characteristic : 10);
    
    while (isalnum(Ch)) {
      mul_si(N, N, base);
      add_si(N, N, isdigit(Ch) ? Ch - '0' : Ch + 10 - (isupper(Ch) ? 'A' : 'a'));
      Ch = ReadCh();
    }
    break;
  }
    
  default:
    Token = GEN;
    GenName.clear();

    while (isalnum(Ch) || Ch == '_' || Ch == '.') {
      GenName.push_back(Ch);
      Ch = ReadCh();
    }

    if (GenName.empty())
      SyntaxError("Illegal character '%c' (ASCII %d) while parsing name", Ch, Ch);

    break;
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
      n->n.init();
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
    node *n = new node{TGEN, GetGen(pres)};
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

#ifdef LIEALG
    if (oper == TPOW && u->type == TGEN && u->g == 0) { // p-power mapping
      FreeNode(u);
      t = new node{TFROB, t};
      continue;
    }
#endif
    if (t->type == TNUM && u->type == TNUM) { // compile-time evaluation
      switch (oper) {
      case TPROD:
	mul(t->n, t->n, u->n);
	break;
      case TPOW:
	pow(t->n, t->n, u->n.get_si());
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
    } else {
      if (oper == TPROD && t->type == TNUM)
	oper = TSPROD;
      if (oper == TPROD && u->type == TNUM) {
	oper = TSPROD;
	std::swap(t, u);
      }
      if (oper == TPOW && u->type != TNUM)
	oper = TCONJ;
      t = new node{oper, t, u};
    }
  }
  return t;
}

static void ValidateExpression(const node *n, gen g) {
  /* check that n is a valid expression, involving only generators of index < g.

     in Lie algebras: forbid TPROD, TINV, TQUO, TLQUO, TREL, TDREL, TPOW, TCONJ.

     in groups: forbid TSUM, TDIFF, TNEG, TREL, TDREL.

     in associative algebras: forbid TQUO, TLQUO, TCONJ, TREL, TDREL.
  */

  switch (n->type) {
  case TNUM:
#ifdef GROUP
    if (n->n.cmp_si(1))
      SyntaxError("Only the constant 1 is allowed as group element");
    break;
#elif defined(LIEALG)
    if (n->n.cmp_si(0))
      SyntaxError("Only the constant 0 is allowed as Lie algebra element");
    break;
#elif defined(ASSOCALG)
    break;    
#endif
  case TGEN:
    if (n->g == 0 || n->g >= g) // generator 0 is for Frobenius map
      SyntaxError("Generator of position < %d expected, not %d", g, n->g);
    break;
    // binary expressions
#ifndef LIEALG
  case TPOW:
    ValidateExpression(n->l, g);
    if (n->r->type != TNUM)
      SyntaxError("RHS ot TPOW should be number, not %s", nodename[n->l->type]);
    break;
#endif
#ifndef GROUP
  case TSPROD:
    if (n->l->type != TNUM)
      SyntaxError("LHS of TSPROD should be number, not %s", nodename[n->l->type]);
    ValidateExpression(n->r, g);
    break;
#endif
  case TBRACK:
  case TPROD:
#ifndef GROUP
  case TSUM:
  case TDIFF:
#endif
#ifdef GROUP
  case TQUO:
  case TLQUO:
  case TCONJ:
#endif    
    ValidateExpression(n->l, g);
    ValidateExpression(n->r, g);
    break;
    // unary
#ifdef LIEALG
  case TFROB:
#endif
#ifndef GROUP
  case TNEG:
#endif
#ifndef LIEALG
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

fppresentation::fppresentation(const char *InputFileName, bool ppower) {
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

  Weight.resize(1); // we start indexing at 1
  GeneratorName.resize(1);
  if (ppower)
    GeneratorName[0] = "p";
  
  Column = 0;
  CurLine = "";
  Line = 1;
  N.init();
  
  NextToken(); // start parsing
  if (Token != LANGLE)
    SyntaxError("'<' expected");

  unsigned weight = 1;

  NextToken();
  /* get generators */
  while (true) {
    while (true) {
      if (Token != SEMICOLON)
	break;
      NextToken();
      weight++;
    }
    if (Token == PIPE)
      break;

    while (true) {
      if (Token != GEN)
	SyntaxError("Generator expected");

      // we start at 0, including the special name "p" at position 0, to recognize p-powers
      for (unsigned i = 0; i <= NrGens; i++) {
	if (GenName == GeneratorName[i])
	  SyntaxError("Duplicate generator %s", GenName.c_str());
      }

      NrGens++;
      GeneratorName.resize(NrGens + 1);
      GeneratorName[NrGens].assign(GenName);
      Weight.resize(NrGens + 1);
      
      NextToken();
      if (Token == POWER) {
	NextToken();
	node *t = Term(*this);
	if (t->type != TNUM)
	  SyntaxError("Number expected as weight of generator %s", GenName.c_str());
	int w = t->n.get_si();
	if (w <= 0)
	  SyntaxError("Weight of generator %s should be positive, not %d", GenName.c_str(), w);
	Weight[NrGens] = w;
      } else
	Weight[NrGens] = weight;
      
      if (Token != COMMA)
	break;
      NextToken();
    }
  }
    
  NextToken();
  /* get relators */
  while (is_relation(Token)) {
    node *n = Expression(*this, 0);

    if (n->type == TDRELR) { /* switch sides */
      n->type = TDREL;
      std::swap(n->l,n->r);
    }
    
    if (n->type == TREL) { /* chains of equalities */
      node *t;
      for (t = n; t->type == TREL; t = t->l)
	ValidateExpression(t->r, LASTGEN);
      ValidateExpression(t, LASTGEN);
    } else if (n->type == TDREL) {
      if (n->l->type != TGEN)
	SyntaxError("LHS should be generator, not %s", nodename[n->l->type]);

      if (!Aliases.empty() && Aliases.back()->l->g >= n->l->g)
	SyntaxError("Definitions are not in increasing order at generator %s", GeneratorName[n->l->g].c_str());
      
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

    if (Debug >= 3) {
      fprintf(LogFile, "# ");
      printnode(LogFile, n);
      fprintf(LogFile,"\n");
    }

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
  
  N.clear();
}

fppresentation::~fppresentation() {
  for (const auto &n : Relators)
    delete n;
  for (const auto &n : Aliases)
    delete n;
  for (const auto &n : Endomorphisms)
    delete n;
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
    fprintf(f, PRIfpcoeff, &n->n);
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
  case TFROB:
    fprintf(f, "(");
    printnode(f, n->u);
    fprintf(f, ")^p");
    break;
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
  case TSPROD:
    printnode(f, n->l);
    fprintf(f, "*(");
    printnode(f, n->r);
    fprintf(f, ")");
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
    fprintf(f, ")^");
    printnode(f, n->r);
    break;
  case TCONJ:
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
