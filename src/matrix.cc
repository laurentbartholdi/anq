/******************************************************************************
**
**                 Nilpotent Quotient for Lie Rings
** matrix.c                                                     Csaba Schneider
**                                                           schcs@math.klte.hu
*/

#include "lienq.h"

static unsigned NrRows;
static gpvec *Matrix;

void InitMatrix(void) {
  Matrix = (gpvec *) malloc(NrCenGens * sizeof(gpvec));
  if (Matrix == NULL)
    abortprintf(2, "InitMatrix: malloc(Matrix) failed");

  NrRows = 0;
}

void FreeMatrix(void) {
  for (unsigned i = 0; i < NrRows; i++)
    FreeVec(Matrix[i], NrTotalGens);
  free(Matrix);
}

/* v -= v[w->g]/w->c * w */
void ReduceRow(gpvec &v, gpvec &w) {
  for (gpvec p = v; p->g != EOW; p++)
    if (p->g == w->g) {
      coeff q;
      coeff_init (q);
      coeff_fdiv_q(q, p->c, w->c);
      if (coeff_nz_p(q)) {
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

void HermiteNormalForm(gpvec **rels, unsigned *numrels) {
  /* reduce all the head columns, to achieve Hermite normal form. */
  for (unsigned i = 1; i < NrRows; i++)
    for (unsigned j = 0; j < i; j++)
      ReduceRow(Matrix[j], Matrix[i]);

  *rels = Matrix;
  *numrels = NrRows;
}

#if 0
/* a failed attempt to improve the matrix code -- I tried to put it after
   each row change, but performance went down */
void PartialHermite(unsigned row) {
  return;
  for (unsigned j = 0; j < row; j++)
    ReduceRow(Matrix[j], Matrix[row]);
  return;
  for (unsigned j = row+1; j < NrRows; j++)
    ReduceRow(Matrix[row], Matrix[j]);
  return;
}
#endif

bool AddRow(gpvec cv) {
  if (cv->g == EOW) // easy case: trivial relation, change nothing
    return false;
  
  if (cv->g <= NrPcGens)
    abortprintf(5, "AddRow: vector has a term a%d not in the centre", cv->g);

  bool ChangedMatrix = false;


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

      for (unsigned i = NrRows++; i > row; i--)
	Matrix[i] = Matrix[i-1];
      Matrix[row] = NewVec(NrTotalGens);
      Prod(Matrix[row], unit, p);

      if (Debug >= 3) {
	printf("ADD ROW %d: ",row); PrintVec(Matrix[row]); printf("\n");
      }

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
	if (Debug >= 3) {
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
