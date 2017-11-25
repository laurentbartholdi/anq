/******************************************************************************
**
**                 Nilpotent Quotient for Lie Rings
** matrix.c                                                     Csaba Schneider
**                                                           schcs@math.klte.hu
*/

#include "lienq.h"

#if 0
#include<gmp.h>
typedef mpz_t large;
#define large_init mpz_init
#define large_clear mpz_clear
#define large_set mpz_set
#define large_set_si mpz_set_si
#define large_get_si mpz_get_si
#define large_fits_slong_p mpz_fits_slong_p

#define large_neg mpz_neg
#define large_sgn mpz_sgn
#define large_mul mpz_mul
#define large_divexact mpz_divexact
#define large_submul mpz_submul
#define large_addmul mpz_addmul
#define large_gcdext mpz_gcdext
#define large_fdiv_q mpz_fdiv_q
#else
typedef long large;
#define large_swap(v,w) {large z; z=v; v=w; w=z;}
#define large_init(z) {z=0;}
#define large_clear(z)
#define large_set(z,v) {z=v;}
#define large_set_si(z,v) {z=v;}
#define large_get_si(z) z
#define large_fits_slong_p(z) true

#define large_neg(z,v) {z=-v;}
#define large_sgn(z) ((z>0)-(z<0))
#define large_mul(z,v,w) {z=v*w;}
#define large_divexact(z,v,w) {z=v/w;}
#define large_submul(z,v,w) {z -= v*w;}
#define large_addmul(z,v,w) {z += v*w;}
#define large_fdiv_q(z,v,w) {z=v/w; if(v-z*w<0) z--;}
/* this code works only if b>0 */
void large_gcdext(large &gcd, large &s, large &t, large a, large b) {
  large new_s, new_t, new_gcd, q;
  large_init(new_s);
  large_init(new_t);
  large_init(new_gcd);  
  large_init(q);  
  large_set_si(new_s, 0); large_set_si(s, 1);
  large_set_si(new_t, 1); large_set_si(t, 0);
  large_set(new_gcd, b); large_set(gcd, a);
  while (large_sgn(new_gcd)) {
    large_fdiv_q(q, gcd, new_gcd);
    large_submul(s, q, new_s); large_swap(s, new_s);
    large_submul(t, q, new_t); large_swap(t, new_t);
    large_submul(gcd, q, new_gcd); large_swap(gcd, new_gcd);
  }
  large_clear(new_s);
  large_clear(new_t);
  large_clear(new_gcd);
  large_clear(q);
}
#endif

typedef large *lvec;

unsigned NrRows, NrCols, *Heads;

large **Matrix;

void InitMatrix(void) {
  if ((Matrix = (lvec *)malloc(200 * sizeof(lvec))) == NULL) {
    perror("AddRow, Matrix ");
    exit(2);
  }
  if ((Heads = (unsigned *)malloc(200 * sizeof(unsigned))) == NULL) {
    perror("AddRow, Heads ");
    exit(2);
  }
  NrCols = NrCenGens;
  NrRows = 0;
}

void FreeVector(lvec v) {
  for (unsigned i = 1; i <= NrCols; i++) {
    large_clear(v[i]);
  }
  free(v);
}

void FreeMatrix(void) {
  for (unsigned i = 0; i < NrRows; i++)
    FreeVector(Matrix[i]);
  free(Matrix);
  free(Heads);
}

void ReduceRow(lvec v, lvec w, unsigned head) {
  large q;
  large_init (q);
  large_fdiv_q(q, v[head], w[head]);
  if (large_sgn(q))
    for (unsigned k = head; k <= NrCols; k++)
      large_submul(v[k], q, w[k]);
  large_clear(q);
}

/*
**    MatrixToExpVec() converts the contents of Matrix[] to a list of
**    exponent vectors which can be used easily by the elimination
**    routines. It also checks that the integers are not bigger than 2^15.
**    If this is the case it prints a warning and aborts.
*/
gpvec *MatrixToExpVecs() {
  if (NrRows == 0)
    return (gpvec *)0;

  /* first reduce all the head columns, to achieve Hermite normal form. */
  for (unsigned i = 1; i < NrRows; i++)
    for (unsigned j = 0; j < i; j++)
      ReduceRow(Matrix[j], Matrix[i], Heads[i]);
  
  gpvec *M = (gpvec *) malloc(NrRows * sizeof(gpvec));
  if (M == NULL) {
    perror("MatrixToExpVecs(), M");
    exit(2);
  }

  /* Convert. */
  for (unsigned i = 0; i < NrRows; i++) {
    M[i] = NewGpVec(NrCols + 1);

    gpvec p = M[i];
    for (unsigned j = Heads[i]; j <= NrCols; j++) {
      if (!large_fits_slong_p(Matrix[i][j])) {
	perror("Exponent cannot fit in a single word");
	exit(4);
      }
      if (large_sgn(Matrix[i][j])) {
	p->g = j + NrPcGens;
	p->c = large_get_si(Matrix[i][j]);
	p++;
      }
    }
    p->g = EOW;
  }

  return M;
}

static bool ChangedMatrix;

/* add row v to Matrix, making sure it remains in Hermite normal form */
void AddRow(lvec v, unsigned head) {
#if 0
  large g, s, t;
  large_gcdext(g, s, t, 11, 4); printf("%ld = 11*%ld + 4*%ld\n", g, s, t);
  large_gcdext(g, s, t, -11, 4); printf("%ld = -11*%ld + 4*%ld\n", g, s, t);
  large_gcdext(g, s, t, 11, -4); printf("%ld = 11*%ld + -4*%ld\n", g, s, t);
  large_gcdext(g, s, t, -11, -4); printf("%ld = -11*%ld + -4*%ld\n", g, s, t);
  exit(1);
#endif
  
  unsigned row;
  for (row = 0; row < NrRows && Heads[row] <= head; row++)
    if (Heads[row] == head) {
      large a, b, c, d, x, y;
      large_init(a);
      large_init(b);
      large_init(d);
      large_gcdext(d, a, b, v[head], Matrix[row][head]); /* d = a*v[head]+b*Matrix[row][head] */
      if (!large_sgn(a)) { /* likely case: Matrix[row][head]=d, b=1, a=0 */
	large_divexact(d,v[head],d);
	for (unsigned i = head; i <= NrCols; i++)
	  large_submul(v[i],d,Matrix[row][i]);
      } else {
	ChangedMatrix = true;
	large_init(c);
	large_init(x);
	large_init(y);
	large_divexact(c,v[head],d);
	large_divexact(d,Matrix[row][head],d);
	for (unsigned i = head; i <= NrCols; i++) {
	  large_mul(x,a,v[i]);
	  large_addmul(x,b,Matrix[row][i]);
	  large_mul(y,c,Matrix[row][i]);
	  large_submul(y,d,v[i]);
	  large_set(Matrix[row][i],x);
	  large_set(v[i],y);
	}
	large_clear(c);
	large_clear(x);
	large_clear(y);
      }
      large_clear(a);
      large_clear(b);
      large_clear(d);

      while (!large_sgn(v[head]))
	if (++head > NrCols) {
	  FreeVector(v);
	  return;
	}
    }

  /* we have a new row to insert. put v in Matrix at row */
  if (large_sgn(v[head]) < 0)
    for (unsigned i = head; i <= NrCols; i++)
      large_neg(v[i], v[i]);
    
  ChangedMatrix = true;
  if (NrRows % 200 == 0) {
    Matrix = (lvec *)realloc(Matrix, (NrRows + 200) * sizeof(lvec));
    if (Matrix == NULL) {
      perror("AddRow, Matrix ");
      exit(2);
    }
    Heads = (unsigned *)realloc(Heads, (NrRows + 200) * sizeof(unsigned));
    if (Heads == NULL) {
      perror("AddRow, Heads ");
      exit(2);
    }
  }

  for (unsigned i = NrRows; i > row; i--) {
    Matrix[i] = Matrix[i-1];
    Heads[i] = Heads[i-1];
  }
  Matrix[row] = v;
  Heads[row] = head;
  NrRows++;  
}

bool AddRow(gpvec gv) {
  lvec v;

  ChangedMatrix = false;

  /* Find the Head of gv */
  for (; gv->g != EOW && !gv->c.notzero(); gv++);
  if (gv->g == EOW)
    return false;

  unsigned head = gv->g - NrPcGens;

  /* Copy the NrCenGens entries of gv and free it. */
  v = (lvec)malloc((NrCols + 1) * sizeof(large));
  if (v == NULL) {
    perror("AddRow, v");
    exit(2);
  }
  for (unsigned i = 1; i <= NrCols; i++)
    large_init (v[i]);
  
  for (; gv->g != EOW; gv++) {
    if (gv->g <= NrPcGens) {
      perror("AddRow has a coefficient not in the center");
      exit(5);
    }
    large_set_si(v[gv->g-NrPcGens], gv->c.data);
  }

  AddRow(v, head);

  return ChangedMatrix;
}
