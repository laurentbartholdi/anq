/******************************************************************************
**
**                 Nilpotent Quotient for Lie Rings
** matrix.c                                                     Csaba Schneider
**                                                           schcs@math.klte.hu
*/

#include "lienq.h"

unsigned NrRows, NrCols, *Heads;

coeffvec *Matrix;

void InitMatrix(void) {
  if ((Matrix = (coeffvec *) malloc(200 * sizeof(coeffvec))) == NULL) {
    perror("InitMatrix, Matrix ");
    exit(2);
  }
  if ((Heads = (unsigned *) malloc(200 * sizeof(unsigned))) == NULL) {
    perror("InitMatrix, Heads ");
    exit(2);
  }
  NrCols = NrCenGens;
  NrRows = 0;
}

void FreeVector(coeffvec v) {
  for (unsigned i = 1; i <= NrCols; i++) {
    coeff_clear(v[i]);
  }
  free(v);
}

void FreeMatrix(void) {
  for (unsigned i = 0; i < NrRows; i++)
    FreeVector(Matrix[i]);
  free(Matrix);
  free(Heads);
}

void ReduceRow(coeffvec v, coeffvec w, unsigned head) {
  coeff q;
  coeff_init (q);
  coeff_fdiv_q(q, v[head], w[head]);
  if (coeff_nz(q))
    for (unsigned k = head; k <= NrCols; k++)
      coeff_submul(v[k], q, w[k]);
  coeff_clear(q);
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
      if (coeff_nz(Matrix[i][j])) {
	p->g = j + NrPcGens;
	coeff_init_set(p->c, Matrix[i][j]);
	p++;
      }
    }
    p->g = EOW;
  }

  return M;
}

static bool ChangedMatrix;

/* add row v to Matrix, making sure it remains in Hermite normal form */
void AddRow(coeffvec v, unsigned head) {
  unsigned row;
  for (row = 0; row < NrRows && Heads[row] <= head; row++)
    if (Heads[row] == head) {
      coeff a, b, c, d, x, y;
      coeff_init(a);
      coeff_init(b);
      coeff_init(d);
      coeff_gcdext(d, a, b, v[head], Matrix[row][head]); /* d = a*v[head]+b*Matrix[row][head] */
      if (!coeff_cmp(d, Matrix[row][head])) { /* likely case: Matrix[row][head]=d, b=1, a=0 */
	coeff_divexact(d,v[head],d);
	for (unsigned i = head; i <= NrCols; i++)
	  coeff_submul(v[i], d, Matrix[row][i]);
      } else {
	ChangedMatrix = true;
	coeff_init(c);
	coeff_init(x);
	coeff_init(y);
	coeff_divexact(c,v[head],d);
	coeff_divexact(d,Matrix[row][head],d);
	for (unsigned i = head; i <= NrCols; i++) {
	  coeff_mul(x, b, Matrix[row][i]);
	  coeff_mul(y, c, Matrix[row][i]);
	  coeff_mul(Matrix[row][i], a, v[i]);
	  coeff_mul(v[i], d, v[i]);
	  coeff_add(Matrix[row][i], Matrix[row][i], x);
	  coeff_sub(v[i], y, v[i]);
	}
	coeff_clear(c);
	coeff_clear(x);
	coeff_clear(y);
      }
      coeff_clear(a);
      coeff_clear(b);
      coeff_clear(d);

      while (!coeff_nz(v[head]))
	if (++head > NrCols) {
	  FreeVector(v);
	  return;
	}
    }

  /* we have a new row to insert. put v in Matrix at row */
  if (coeff_sgn(v[head]) < 0)
    for (unsigned i = head; i <= NrCols; i++)
      coeff_neg(v[i], v[i]);
    
  ChangedMatrix = true;
  if (NrRows % 200 == 0) {
    Matrix = (coeffvec *)realloc(Matrix, (NrRows + 200) * sizeof(coeffvec));
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

bool AddRow(coeffvec cv) {
  coeffvec v;
  unsigned head;
  
  ChangedMatrix = false;

  /* Find the Head of gv */
  for (head = 1; ; head++) {
    if (head > NrTotalGens) return false;
    if (coeff_nz(cv[head])) break;
  }
      
  if (head <= NrPcGens) {
    perror("AddRow has a coefficient not in the center");
    exit(5);
    }

  /* Copy the NrCenGens entries of gv */
  v = (coeffvec) malloc((NrCols + 1) * sizeof(coeff));
  if (v == NULL) {
    perror("AddRow, v");
    exit(2);
  }
  for (unsigned i = 1; i <= NrCols; i++)
    coeff_init_set(v[i], cv[i + NrPcGens]);

  AddRow(v, head - NrPcGens);

  return ChangedMatrix;
}
