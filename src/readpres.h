/******************************************************************************
**
**               Nilpotent Quotient for Lie Algebras
** readpres.h                                                   Csaba Schneider
**                                                           schcs@math.klte.hu
*/

unsigned NrRels, NrGens;

/*
** The following date structure will represent a node in the expression tree.
** A node has a type entry and a content. The content can be integer (ring-
** element), generator (lie-ring-element), or binary operation depending on
** the type.


struct _node {
  int type;
  union {
      int n;
      int g;
      struct { struct _node *l, *r; } op;
    } cont;
};


typedef struct _node node;
*/

/*
** The following macros define the type of a node. It can be number, generator
** or binary operation.
*/

#define TNUM 1
#define TGEN 2

#define TMPROD 3
#define TLPROD 4
#define TSUM 5
#define TREL 6
#define TDRELL 7
#define TDRELR 8
#define TLAST 9

extern void Presentation();

static int Ch;            /* Contains the next char on the input. */
static int Token;         /* Contains the current token. */
static int Line;          /* Current line number. */
static int TLine;         /* Line number where token starts. */
static int Char;          /* Current character number. */
static int TChar;         /* Character number where token starts. */
static char *InFileName;  /* Current input file name. */
static FILE *InFp;        /* Current input file pointer. */
static long long N;       /* Contains the integer just read. */
static char Gen[128];     /* Contains the generator name. */
#if 0
static const char *TokenName[] = {
    "",       "LParen", "RParen", "LBrack",  "RBrack",  "LBrace", "RBrace",
    "Mult",   "Power",  "Equal",  "DEqualL", "DEqualR", "Plus",   "Minus",
    "LAngle", "RAngle", "Pipe",   "Comma",   "Number",  "Gen"};
#endif
/*
**    The following macros define tokens.
*/
#define LPAREN 1
#define RPAREN 2
#define LBRACK 3
#define RBRACK 4
#define LBRACE 5
#define RBRACE 6

#define MULT 7
#define POWER 8
#define EQUAL 9
#define DEQUALL 10
#define DEQUALR 11

#define PLUS 12
#define MINUS 13

#define LANGLE 14
#define RANGLE 15

#define PIPE 16
#define COMMA 17
#define SEMICOLON 18
#define NUMBER 19
#define GEN 20

/* The following structura will carry the presentation given by the user. */

PresStruct Pres;
