/******************************************************************************
**
**                 Nilpotent Quotient for Lie Rings
** matrix.c                                                     Csaba Schneider
**                                                           schcs@math.klte.hu
*/

#include "lienq.h"

unsigned NrRows, NrCols;

gpvec *Matrix;

void InitMatrix(void) {
  if ((Matrix = (gpvec *) malloc(200 * sizeof(gpvec))) == NULL) {
    perror("InitMatrix, Matrix ");
    exit(2);
  }
  NrCols = NrCenGens;
  NrRows = 0;
}

void FreeMatrix(void) {
  for (unsigned i = 0; i < NrRows; i++)
    FreeGpVec(Matrix[i]);
  free(Matrix);
}

/* v -= v[w->g]/w->c * w */
void ReduceRow(gpvec &v, gpvec &w) {
  for (gpvec p = v; p->g != EOW; p++)
    if (p->g == w->g) {
      coeff q;
      coeff_init (q);
      coeff_fdiv_q(q, p->c, w->c);
      if (coeff_nz(q)) {
	gpvec n = NewGpVec(NrCols);
	Diff(n, v, q, w);
	FreeGpVec(v);
	coeff_clear(q);
	v = n;
	break;
      }
    }
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
      ReduceRow(Matrix[j], Matrix[i]);

  return Matrix;
}

static bool ChangedMatrix;

/* add row v to Matrix, making sure it remains in Hermite normal form */
void AddRow(coeffvec v, unsigned head) {
  unsigned row;
  for (row = 0; row < NrRows && Matrix[row]->g <= head; row++)
    if (Matrix[row]->g == head) {
      coeff a, b, c, d, x, y;
      coeff_init(a);
      coeff_init(b);
      coeff_init(d);
      coeff_gcdext(d, a, b, v[head], Matrix[row]->c); /* d = a*v[head]+b*Matrix[row][head] */
      if (!coeff_cmp(d, Matrix[row]->c)) { /* likely case: Matrix[row][head]=d, b=1, a=0 */
	coeff_divexact(d,v[head],d);
	for (gpvec p = Matrix[row]; p->g != EOW; p++)
	  coeff_submul(v[p->g], d, p->c);
      } else {
	ChangedMatrix = true;
	coeffvec w = NewCoeffVec();
	coeff_init(c);
	coeff_init(x);
	coeff_init(y);
	coeff_divexact(c,v[head],d);
	coeff_divexact(d,Matrix[row]->c,d);
	for (unsigned i = head; i <= NrTotalGens; i++) {
	  coeff_mul(w[i], a, v[i]);
	  coeff_mul(v[i], d, v[i]);
	}
	for (gpvec p = Matrix[row]; p->g != EOW; p++) {
	  coeff_addmul(w[p->g], b, p->c);
	  coeff_submul(v[p->g], c, p->c);
	}
	FreeGpVec(Matrix[row]);
	Matrix[row] = CoeffVecToGpVec(w);
	FreeCoeffVec(w);
	coeff_clear(c);
	coeff_clear(x);
	coeff_clear(y);
      }
      coeff_clear(a);
      coeff_clear(b);
      coeff_clear(d);

      while (!coeff_nz(v[head]))
	if (++head > NrTotalGens)
	  return;
    }

  /* we have a new row to insert. put v in Matrix at row */
  gpvec gv = CoeffVecToGpVec(v);
  if (coeff_sgn(v[head]) < 0)
    ModNeg(gv);
    
  ChangedMatrix = true;
  if (NrRows % 200 == 0) {
    Matrix = (gpvec *) realloc(Matrix, (NrRows + 200) * sizeof(gpvec));
    if (Matrix == NULL) {
      perror("AddRow, Matrix ");
      exit(2);
    }
  }

  for (unsigned i = NrRows; i > row; i--)
    Matrix[i] = Matrix[i-1];
  Matrix[row] = gv;
  NrRows++;  
}

bool AddRow(coeffvec cv) {
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

  AddRow(cv, head);

  return ChangedMatrix;
}
