/******************************************************************************
**
**                 Nilpotent Quotient for Lie Rings
** matrix.c                                                     Csaba Schneider
**                                                           schcs@math.klte.hu
*/

#include "lienq.h"

unsigned NrRows;

gpvec *Matrix;

void InitMatrix(void) {
  if ((Matrix = (gpvec *) malloc(NrCenGens * sizeof(gpvec))) == NULL) {
    perror("InitMatrix, Matrix ");
    exit(2);
  }
  NrRows = 0;
}

void FreeMatrix(void) {
  for (unsigned i = 0; i < NrRows; i++)
    FreeVec(Matrix[i]);
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
	gpvec temp = FreshVec();
	Diff(temp, v, q, w);
	Copy(v, temp);
	PopVec();
	coeff_clear(q);
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

bool AddRow(gpvec cv) {
  bool ChangedMatrix = false;

  if (cv->g != EOW && cv->g <= NrPcGens) {
    perror("AddRow has a coefficient not in the center");
    exit(5);
  }

  gpvec p = FreshVec();
  Copy(p, cv);
  
  for (unsigned row = 0; p->g != EOW; row++) {
    if (row >= NrRows || Matrix[row]->g > p->g) {
      /* Insert v in Matrix at position row */
      ChangedMatrix = true;

      coeff unit, annihilator;
      coeff_init(unit);
      coeff_init(annihilator);
      coeff_unit_annihilator(unit, annihilator, p->c);

      for (unsigned i = NrRows; i > row; i--)
	Matrix[i] = Matrix[i-1];
      Matrix[row] = NewVec(NrTotalGens);
      Prod(Matrix[row], unit, p);
      if (Debug >= 2) {
	printf("ADD ROW %d: ",row); PrintVec(Matrix[row]); printf("\n");
      }
      NrRows++;

      Prod(p, annihilator, p);
      coeff_clear(unit);
      coeff_clear(annihilator);
    } else if (Matrix[row]->g == p->g) { /* two rows with same pivot. Merge them */
      coeff a, b, c, d;
      coeff_init(a);
      coeff_init(b);
      coeff_init(c);
      coeff_init(d);
      coeff_gcdext(d, a, b, p->c, Matrix[row]->c); /* d = a*v[head]+b*Matrix[row][head] */
      if (!coeff_cmp(d, Matrix[row]->c)) { /* likely case: Matrix[row][head]=d, b=1, a=0 */
	coeff_divexact(d,p->c,d);
	gpvec temp = FreshVec();
	Diff(temp, p, d, Matrix[row]);
#if 0
	PopVec(p);
#else
	Copy(p, temp);
	PopVec();
#endif
	
      } else {
	ChangedMatrix = true;
	coeff_divexact(c,p->c,d);
	coeff_divexact(d,Matrix[row]->c,d);
	gpvec newp = FreshVec();
	gpvec newrow = FreshVec();
	Sum(newrow, a, p, b, Matrix[row]);
	Diff(newp, c, Matrix[row], d, p);
#if 0
	PopVec(Matrix[row]); // pops newrow. Works only if Matrix allocated on stack
#else	
	Copy(Matrix[row], newrow);
	PopVec(); // pops newrow
#endif
#if 0
	PopVec(p);
#else
	Copy(p, newp);
	PopVec();
#endif
	if (Debug >= 2) {
	  printf("CHANGE ROW %d: ",row); PrintVec(Matrix[row]); printf("\n");
	}
      }
      coeff_clear(a);
      coeff_clear(b);
      coeff_clear(c);
      coeff_clear(d);
    }
  }

  PopVec(); // free p
  
  return ChangedMatrix;
}
