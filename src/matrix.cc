/******************************************************************************
**
**                 Nilpotent Quotient for Lie Rings
** matrix.c                                                     Csaba Schneider
**                                                           schcs@math.klte.hu
*/

#include "lienq.h"
#include <algorithm>

static unsigned NrRows, FirstCentral;
static gpvec *Matrix;

void InitMatrix(pcpresentation &pc) {
  FirstCentral = pc.NrPcGens + 1;
  unsigned nrcentralgens = NrTotalGens-pc.NrPcGens;
  Matrix = (gpvec *) malloc((nrcentralgens+1) * sizeof(gpvec));
  if (Matrix == NULL)
    abortprintf(2, "InitMatrix: malloc(Matrix) failed");

  if (pc.TorsionExp == 0)
    NrRows = 0;
  else {
    NrRows = nrcentralgens;
    for (unsigned i = 0; i < nrcentralgens; i++) {
      Matrix[i] = NewVec(NrTotalGens);
      Matrix[i][0].g = pc.NrPcGens + i + 1;
      coeff_set_si(Matrix[i][0].c, pc.TorsionExp);
      Matrix[i][1].g = EOW;
    }
  }

  Matrix[NrRows] = NewVec(NrTotalGens); // scratch row
}

void FreeMatrix(void) {
  for (unsigned i = 0; i <= NrRows; i++)
    FreeVec(Matrix[i], NrTotalGens);
  free(Matrix);
}

inline void SwapRows(unsigned i, unsigned j) {
  gpvec v = Matrix[i];
  Matrix[i] = Matrix[j];
  Matrix[j] = v;
}

/* v -= v[w->g]/w->c * w */
void ReduceRow(unsigned row, gpvec &w) {
  for (gpvec p = Matrix[row]; p->g != EOW; p++)
    if (p->g == w->g) {
      coeff q;
      coeff_init (q);
      coeff_fdiv_q(q, p->c, w->c);
      if (coeff_nz_p(q)) {
	Diff(Matrix[NrRows], Matrix[row], q, w);
	SwapRows(row, NrRows);
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
      ReduceRow(j, Matrix[i]);

  *rels = Matrix;
  *numrels = NrRows;
}

#if 0
/* a failed attempt to improve the matrix code -- I tried to put it after
   each row change, but performance went down */
void PartialHermite(unsigned row) {
  return;
  for (unsigned j = 0; j < row; j++)
    ReduceRow(j, Matrix[row]);
  return;
  for (unsigned j = row+1; j < NrRows; j++)
    ReduceRow(row, Matrix[j]);
  return;
}
#endif

/* adds a row to the current matrix, and returns true if the matrix was
   modified.
   the vector cv may be modified during the process */
bool AddRow(gpvec cv) {
  if (cv->g == EOW) // easy case: trivial relation, change nothing
    return false;
  
  if (cv->g < FirstCentral)
    abortprintf(5, "AddRow: vector has a term a%d not in the centre", cv->g);

  bool ChangedMatrix = false;

  gpvec p[2] = { cv, FreshVec() };
  bool parity = false;
  
  for (unsigned row = 0; p[parity]->g != EOW; row++) {
    if (row >= NrRows || Matrix[row]->g > p[parity]->g) {
      /* Insert v in Matrix at position row */
      ChangedMatrix = true;

      coeff unit, annihilator;
      coeff_init(unit);
      coeff_init(annihilator);
      coeff_unit_annihilator(unit, annihilator, p[parity]->c);

      for (unsigned i = ++NrRows; i > row; i--)
	Matrix[i] = Matrix[i-1];
      Matrix[row] = NewVec(NrTotalGens);
      Prod(Matrix[row], unit, p[parity]);

      for (unsigned j = row+1; j < NrRows; j++)
	ReduceRow(row, Matrix[j]);

      if (Debug >= 3) {
	fprintf(LogFile, "# Adding row %d: ",row); PrintVec(LogFile, Matrix[row]); fprintf(LogFile, "\n");
      }

      Prod(p[parity], annihilator, p[parity]);
      coeff_clear(unit);
      coeff_clear(annihilator);
    } else if (Matrix[row]->g == p[parity]->g) { /* two rows with same pivot. Merge them */
      coeff a, b, c, d;
      coeff_init(a);
      coeff_init(b);
      coeff_init(c);
      coeff_init(d);
      coeff_gcdext(d, a, b, p[parity]->c, Matrix[row]->c); /* d = a*v[head]+b*Matrix[row][head] */
      if (!coeff_cmp(d, Matrix[row]->c)) { /* likely case: Matrix[row][head]=d, b=1, a=0 */
	coeff_divexact(d, p[parity]->c, d);
	Diff(p[!parity], p[parity], d, Matrix[row]);
	parity ^= 1;	
	//ReduceRow(row, p[parity]); // actually slows down the code
#ifdef COEFF_IS_MPZ // check coefficient explosion
      if (Debug >= 1) {
	long maxsize = 0;
	for (gpvec q = p[parity]; q->g != EOW; q++)
	  maxsize = std::max(maxsize, labs(q->c->_mp_size));
	fprintf(LogFile, "# Changed p: max coeff size %ld\n", maxsize);
      }
#endif
	
      } else {
	ChangedMatrix = true;

	coeff_divexact(c, p[parity]->c, d);
	coeff_divexact(d, Matrix[row]->c, d);
	Sum(Matrix[NrRows], a, p[parity], b, Matrix[row]);
	Diff(p[!parity], c, Matrix[row], d, p[parity]);
	SwapRows(row, NrRows);
	parity ^= 1;
	//ReduceRow(row, p[parity]); // actually slows down the code

	if (Debug >= 3) {
	  fprintf(LogFile, "# Change row %d: ",row); PrintVec(LogFile, Matrix[row]); fprintf(LogFile, "\n");
	}
      }
      coeff_clear(a);
      coeff_clear(b);
      coeff_clear(c);
      coeff_clear(d);
    }
  }

  PopVec(); // free p[true]
  
  return ChangedMatrix;
}
