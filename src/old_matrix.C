/******************************************************************************
**
**                 Nilpotent Quotient for Lie Rings
** matrix.c                                                     Csaba Schneider
**                                                           schcs@math.klte.hu
*/

#include "lienq.h"
/* pow is a builtin for C++11 */
#define pow mp_pow
extern "C" {
#include "mp.h"
}
typedef MINT *large;
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

void freeVector(lvec v) {
  for (unsigned i = 1; i <= NrCols; i++) {
    mfree(v[i]);
  }
  free((void *)v);
}

void FreeMatrix(void) {
  for (unsigned i = 0; i < NrRows; i++)
    freeVector(Matrix[i]);
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
      large m = Matrix[i][j];
      if (m->size != 0) {
	if (labs(m->size) > 1) {
	  perror("Exponent cannot fit in a single word");
	  exit(4);
	}
        p->g = j + NrPcGens;
	p->c = m->size * m->d[0];
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
    v[a]->size = -v[a]->size;
    a++;
  }
}

void vSubOnce(lvec v, lvec w, unsigned a) {
  while (a <= NrCols) {
    msub(v[a], w[a], v[a]);
    a++;
  }
}

void vSub(lvec v, lvec w, unsigned a) {
  large s, t;

  if (v[a]->size != 0) {
    s = itom(0);
    t = itom(0);
    mdiv(v[a], w[a], s, t);
    if (s->size != 0)
      while (a <= NrCols) {
        mult(s, w[a], t);
        msub(v[a], t, v[a]);
        a++;
      }

    mfree(s);
    mfree(t);
  }
}

static bool ChangedMatrix;

large ltom(coeff n) {
  char x[20];
  large l;

  int d = n.data;
  
  if (labs(d) >= 1 << 15) {
    sprintf(x, "%lx", labs(d));
    l = xtom(x);
    if (d < 0)
      l->size = -l->size;
    return l;
  } else
    return itom(d);
}

/*
**    VReduce() reduces the vector v against the vectors in Matrix[].
*/
bool VReduce(lvec &v, unsigned &head) {
  for (unsigned i = 0; i < NrRows && Heads[i] <= head; i++) {
    if (Heads[i] == head) {
      while (v[head]->size != 0 && Matrix[i][head]->size != 0) {
        vSub(v, Matrix[i], head);
        if (v[head]->size != 0) {
          ChangedMatrix = true;
          vSub(Matrix[i], v, head);
        }
      }
      if (v[head]->size != 0) { /* v replaces the i-th row. */
        if (v[head]->size < 0)
          vNeg(v, head);
        lvec w = Matrix[i];
        Matrix[i] = v;
        v = w;
      }
      while (head <= NrCols && v[head]->size == 0)
        head++;
      if (head > NrCols)
	return false;
    }
  }
  if (head <= NrCols && v[head]->size < 0)
    vNeg(v, head);
  return true;
}

/* This function adds a row to Matrix, which is preserved
   in Hermite normal form */
bool AddRow(gpvec gv) {
  coeffvec cv = GpVecToCoeffVec(gv);
  lvec v;
  unsigned head = 0;

  ChangedMatrix = false;

  /* Find the Head of cv */
  for (unsigned i = 1; i <= NrCols; i++)
    if (cv[NrPcGens + i].notzero()) {
      head = i;
      break;
    }
  /* Free cv and return if it is nullvector. */
  if (head == 0) {
    free(cv);
    return false;
  }
  /* Copy the NrCenGens entries of cv and free it. */
  v = (lvec)malloc((NrCols + 1) * sizeof(large));
  if (v == NULL) {
    perror("AddRow, v");
    exit(2);
  }
  for (unsigned i = 1; i <= NrCols; i++)
    v[i] = ltom(cv[NrPcGens + i]);
  free(cv);

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
    freeVector(v);

  /* Reduce all the head columns. */
  for (unsigned i = 1; i < NrRows; i++)
    for (unsigned j = 0; j < i; j++)
      vSub(Matrix[j], Matrix[i], Heads[i]);

  return ChangedMatrix;
}
