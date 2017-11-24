/******************************************************************************
**
**               Nilpotent Quotient for Lie Algebras
** lietype.h                                                    Csaba Schneider
**                                                           schcs@math.klte.hu
*/

typedef unsigned gen;
#define EOW ((gen)0)

/* define MOD2 if we do modular arithmetic modulo a large power of 2 */
//#define MOD2

struct coeff {
#ifdef MOD2
  unsigned
#endif
  long data;
  coeff(void) {}
  coeff(long d) { data = d; }
  coeff operator-(void) { return -this->data; }
  coeff operator*(coeff c) { return this->data * c.data; }
  coeff operator*=(coeff c) { return this->data *= c.data; }
  coeff operator-(coeff c) { return this->data - c.data; }
  coeff operator-=(coeff c) { return this->data -= c.data; }
  coeff operator+(coeff c) { return this->data + c.data; }
  coeff operator+=(coeff c) { return this->data += c.data; }
  bool notone(void) { return this->data != 1; }
  bool notzero(void) { return this->data != 0; }
  coeff reduce(coeff c) { /* the value m such that (*this)-m*c is reduced.
                           we can assume c is nonnegative. */
    if (c.data == 0)
      return 0; /* no possible reduction */
    long m = this->data / c.data;
#ifndef MOD2
    if (this->data - m * c.data < 0)
      m--; /* C rounds to 0, not down */
#endif
    return m;
  }
};
typedef coeff *coeffvec;

struct gpower {
  gen g;
  coeff c;
};
typedef gpower *gpvec;

/*
** An element in a lie-algebra is a sum of several multiplications. Hence it
** will be represented as a expresson-tree. For simplicity (from the user's
** point of view) wi allow four binary operations, i.e.: multiplying two
** generators (lie-product), adding two generators (w. r. t. the module),
** multiplying an integer and a generator (w. r. t. the module) and wi also
** allow the power of a generator to an integer exponent (lie-product).
*/
struct node {
  int type;
  union {
    coeff n;
    gen g;
    struct {
      node *l, *r;
    } op;
  } cont;
};

struct PresStruct {
  unsigned NrGens, NrRels;
  char **Generators;
  node **Relators;
};

struct deftype {
  gen g;
  gen h;
};
