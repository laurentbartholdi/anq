/******************************************************************************
**
**                 Nilpotent Quotient for Lie Rings
** matrix.c                                                     Csaba Schneider
**                                                           schcs@math.klte.hu
*/

#include "lienq.h"

unsigned NrRows;

gpvec *Matrix;

gpvec temp1, temp2, temp3, temp4, temp5;

void InitMatrix(void) {
  if ((Matrix = (gpvec *) malloc(NrCenGens * sizeof(gpvec))) == NULL) {
    perror("InitMatrix, Matrix ");
    exit(2);
  }
  NrRows = 0;

  temp1 = NewGpVec(NrTotalGens);
  temp2 = NewGpVec(NrTotalGens);
  temp3 = NewGpVec(NrTotalGens);
  temp4 = NewGpVec(NrTotalGens);
  temp5 = NewGpVec(NrTotalGens);
}

void FreeMatrix(void) {
  for (unsigned i = 0; i < NrRows; i++)
    FreeGpVec(Matrix[i]);
  free(Matrix);

  FreeGpVec(temp1);
  FreeGpVec(temp2);
  FreeGpVec(temp3);
  FreeGpVec(temp4);
  FreeGpVec(temp5);
}

/* v -= v[w->g]/w->c * w */
void ReduceRow(gpvec &v, gpvec &w) {
  for (gpvec p = v; p->g != EOW; p++)
    if (p->g == w->g) {
      coeff q;
      coeff_init (q);
      coeff_fdiv_q(q, p->c, w->c);
      if (coeff_nz(q)) {
	Diff(temp1, v, q, w);
	coeff_clear(q);
	{ gpvec t; t = v; v = temp1; temp1 = t; }
	break;
      }
      coeff_clear(q);
    }
}

/*
**    MatrixToExpVec() converts the contents of Matrix[] to a list of
**    exponent vectors which can be used easily by the elimination
**    routines. It also checks that the integers are not bigger than 2^15.
**    If this is the case it prints a warning and aborts.
*/
gpvec *MatrixToExpVecs(void) {
  /* first reduce all the head columns, to achieve Hermite normal form. */
  for (unsigned i = 1; i < NrRows; i++)
    for (unsigned j = 0; j < i; j++)
      ReduceRow(Matrix[j], Matrix[i]);

  return Matrix;
}

static bool ChangedMatrix;

/* add row temp5 to Matrix, making sure it remains in Hermite normal form */
void AddRow(void) {
  unsigned row;
  gpvec p = temp5;
  for (row = 0; row < NrRows && Matrix[row]->g <= p->g; row++) /* relies on EOW being the minimal generator */
    if (Matrix[row]->g == p->g) {
      coeff a, b, c, d;
      coeff_init(a);
      coeff_init(b);
      coeff_init(c);
      coeff_init(d);
      coeff_gcdext(d, a, b, p->c, Matrix[row]->c); /* d = a*v[head]+b*Matrix[row][head] */
      if (!coeff_cmp(d, Matrix[row]->c)) { /* likely case: Matrix[row][head]=d, b=1, a=0 */
	coeff_divexact(d,p->c,d);
	Diff(temp1, p, d, Matrix[row]);
	{ gpvec t = temp5; p = temp5 = temp1; temp1 = t; }
      } else {
	ChangedMatrix = true;
	coeff_divexact(c,p->c,d);
	coeff_divexact(d,Matrix[row]->c,d);
	ModProd(temp1, a, p);
	Sum(temp2, temp1, b, Matrix[row]);
	ModProd(temp3, c, Matrix[row]);
	Diff(temp4, temp3, d, p);
	{ gpvec t = Matrix[row]; Matrix[row] = temp2; temp2 = t; }
	{ gpvec t = temp5;  p = temp5 = temp4; temp4 = t; }
	//	printf("CHANGE ROW %d: ",row); PrintGpVec(Matrix[row]); printf("\n");
      }
      coeff_clear(a);
      coeff_clear(b);
      coeff_clear(c);
      coeff_clear(d);
    }

  if (p->g == EOW)
    return;
  
  /* we have a new row to insert. put v in Matrix at row */
  gpvec newgv = NewGpVec(NrTotalGens);
  if (coeff_sgn(p->c) < 0)
    ModNeg(newgv, p);
  else
    CpVec(newgv, p);
  ChangedMatrix = true;
  //  printf("ADD ROW %d: ",row); PrintGpVec(newgv); printf("\n");
  for (unsigned i = NrRows; i > row; i--)
    Matrix[i] = Matrix[i-1];
  Matrix[row] = newgv;
  NrRows++;  
}

bool AddRow(coeffvec cv) {
  ChangedMatrix = false;

  { gpvec gv1 = CoeffVecToGpVec(cv); CpVec(temp5, gv1); FreeGpVec(gv1); }

  if (temp5->g == EOW) // trivial relation
    return false;

  if (temp5->g <= NrPcGens) {
    perror("AddRow has a coefficient not in the center");
    exit(5);
  }

  AddRow();

  return ChangedMatrix;
}
