/******************************************************************************
**
**                 Nilpotent Quotient for Lie Rings
** matrix.c                                                     Csaba Schneider
**                                                           schcs@math.klte.hu
*/

#include "lienq.h"
#include<gmp.h>

typedef mpz_t large;
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
    mpz_clear(v[i]);
  }
  free(v);
}

void FreeMatrix(void) {
  for (unsigned i = 0; i < NrRows; i++)
    FreeVector(Matrix[i]);
  free(Matrix);
  free(Heads);
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
      if (!mpz_fits_slong_p(Matrix[i][j])) {
	perror("Exponent cannot fit in a single word");
	exit(4);
      }
      if (mpz_sgn(Matrix[i][j])) {
	p->g = j + NrPcGens;
	p->c = mpz_get_si(Matrix[i][j]);
	p++;
      }
    }
    p->g = EOW;
  }

  return M;
}

/*
**    The following routines perform operations with vectors :
**
**    vNeg()  negates each entry of the vector v starting at v[a].
**    vSub()  subtracts a multiple of the vector w from the vector v.
**            The scalar w is multiplied with is v[a]/w[a], so that
**            the entry v[a] after the subtraction is smaller than
**            w[a].
**    vSubOnce()  subtracts the vector w from the vector v.
*/
void vNeg(lvec v, unsigned a) {
  while (a <= NrCols) {
    mpz_neg(v[a], v[a]);
    a++;
  }
}

void vSub(lvec v, lvec w, unsigned a) {
  large quotient;

  if (!mpz_sgn(v[a]))
    return;
  
  mpz_init(quotient);
  mpz_fdiv_q(quotient, v[a], w[a]);
  if (mpz_sgn(quotient))
    while (a <= NrCols) {
      mpz_submul(v[a], quotient, w[a]);
      a++;
    }
  
  mpz_clear(quotient);
}

static bool ChangedMatrix;

/*
**    VReduce() reduces the vector v against the vectors in Matrix[].
*/
bool VReduce(lvec &v, unsigned &head) {
  for (unsigned i = 0; i < NrRows && Heads[i] <= head; i++) {
    if (Heads[i] == head) {
      while (mpz_sgn(v[head]) && mpz_sgn(Matrix[i][head])) {
        vSub(v, Matrix[i], head);
        if (mpz_sgn(v[head])) {
          ChangedMatrix = true;
          vSub(Matrix[i], v, head);
        }
      }
      if (mpz_sgn(v[head])) { /* v replaces the i-th row. */
        if (mpz_sgn(v[head]) < 0)
          vNeg(v, head);
        lvec w = Matrix[i];
        Matrix[i] = v;
        v = w;
      }
      while (head <= NrCols && !mpz_sgn(v[head]))
        head++;
      if (head > NrCols)
	return false;
    }
  }
  if (head <= NrCols && mpz_sgn(v[head]) < 0)
    vNeg(v, head);
  return true;
}

void AddRow(lvec v, unsigned head) {
  if (VReduce(v, head)) {
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
    /* Insert v such that Heads[] is in increasing order */
    unsigned pos = NrRows;
    for (; pos > 0; pos--)
      if (Heads[pos-1] > head) {
	Matrix[pos] = Matrix[pos - 1];
	Heads[pos] = Heads[pos - 1];
      } else break;
    Matrix[pos] = v;
    Heads[pos] = head;
    NrRows++;
  } else
    FreeVector(v);

  /* Reduce all the head columns. */
  for (unsigned i = 1; i < NrRows; i++)
    for (unsigned j = 0; j < i; j++)
      vSub(Matrix[j], Matrix[i], Heads[i]);
}

/* mpz_gcdext(g,s,t,a,b) sets g,s,t with 0<g=sa+tb */

/* This function adds a row to Matrix, which is preserved
   in Hermite normal form */
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
    mpz_init (v[i]);
  
  for (; gv->g != EOW; gv++) {
    if (gv->g <= NrPcGens) {
      perror("AddRow has a coefficient not in the center");
      exit(5);
    }
    mpz_set_si(v[gv->g-NrPcGens], gv->c.data);
  }

  AddRow(v, head);

  return ChangedMatrix;
}
