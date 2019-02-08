/******************************************************************************
**
**                 Nilpotent Quotient for Lie Rings
** matrix.c                                                     Csaba Schneider
**                                                           schcs@math.klte.hu
*/

#include "nq.h"
#include "colamd.h"
#include <algorithm>
#include <set>
#include <utility>

/* static variables, cached from InitMatrix */
unsigned NrCols, FirstCentral;
bool Torsion;
const coeff *TorsionExp;

std::vector<sparsecvec> Matrix;

#ifdef HACK_to_allow_pointer_to_be_changed_in_set
struct __sparsecvec { mutable sparsecvec v; };
std::set<__sparsecvec,bool(*)(__sparsecvec,__sparsecvec)> Queue([](__sparsecvec v1, __sparsecvec v2){ return Compare(v1.v,v2.v) < 0; });

then "Matrix.insert(Matrix.end(), Queue.begin(), Queue.end());" should become
std::transform(Queue.begin(), Queue.end(), std::back_inserter(Matrix), [](__sparsecvec v) { return v.v; });

and "Queue.insert(cv);" should become
{
  __sparsecvec xv = {.v = cv};
  auto p = Queue.emplace(xv);
}
#endif

std::set<sparsecvec,bool(*)(sparsecvec,sparsecvec)> Queue([](sparsecvec v1, sparsecvec v2){ return Compare(v1,v2) < 0; });

static void InitTorsion(void) {  
  if (Torsion) {
    for (unsigned i = 0; i < NrCols; i++) {
      Matrix[i].alloc(1);
      Matrix[i][0].first = FirstCentral + i;
      coeff_set(Matrix[i][0].second, *TorsionExp);
      Matrix[i].truncate(1);
    }
  }
}

void InitRelMatrix(const pcpresentation &pc, unsigned nrcentralgens) {
  FirstCentral = pc.NrPcGens + 1;
  NrCols = nrcentralgens;
  Torsion = pc.PAlgebra;
  TorsionExp = &pc.TorsionExp;

  Matrix.resize(NrCols, sparsecvec(nullptr));
  InitTorsion();
}

void FreeRelMatrix(void) {
  if (!Queue.empty())
    abortprintf(5, "FreeMatrix: row queue not empty");
  
  for (sparsecvec v : Matrix)
    v.free(NrCols);
  Matrix.clear();
}

// for debugging purposes
void PrintMatrix(void) {
  for (const sparsecvec v : Matrix)
    if (v.allocated())
      PrintVec(stdout, v);
  printf("\n");
}

std::vector<int> colamd(relmatrix &m) {
  std::vector<int> ind;
  int stats[COLAMD_STATS];
  std::vector<int> intmat;

  for (const sparsecvec v : m) {
    ind.push_back(intmat.size());
    for (auto kc : v)
      intmat.push_back(kc.first - FirstCentral);
  }
  ind.push_back(intmat.size());

  if (Debug >= 2) {
    fprintf(LogFile, "# about to collect %ld relations (%ld nnz)\n", m.size(), intmat.size());
  }

  size_t alloc = colamd_recommended(intmat.size(), NrCols, m.size());
  intmat.reserve(alloc);
  int ok = colamd(NrCols, m.size(), alloc, intmat.data(), ind.data(), NULL, stats);
  if (Debug >= 3) {
    colamd_report(stats);
    fprintf(LogFile, "# row permutation:");
    for (unsigned i = 0; i < m.size(); i++)
      fprintf(LogFile, " %u", ind[i]);
    fprintf(LogFile,"\n");
  }
      
  if (!ok)
    abortprintf(5, "colamd error %d", ok);

  return ind;
}

/* collect the vectors in Queue and Matrix, and combine them back into Matrix */
void LU(void) {
  /* remove unbound entries in Matrix */
  Matrix.erase(std::remove(Matrix.begin(), Matrix.end(), sparsecvec(nullptr)), Matrix.end());

  /* put queue at bottom of matrix */
  Matrix.insert(Matrix.end(), Queue.begin(), Queue.end());  
  Queue.clear();

  /* call colamd to determine optimal insertion ordering */
  std::vector<int> ind = colamd(Matrix);
  
  std::vector<sparsecvec> oldrels(NrCols, sparsecvec(nullptr));
  Matrix.swap(oldrels);
  InitTorsion();

  coeff a, b, c, d;
  coeff_init(a);
  coeff_init(b);
  coeff_init(c);
  coeff_init(d);

  /* add rows of oldrels into Matrix, reducing them along the way, and in
     the order specified by the permutation ind */
  for (unsigned i = 0; i < oldrels.size(); i++) {
    hollowcvec currow = vecstack.fresh();
    currow.copysorted(oldrels[ind[i]]);
    oldrels[ind[i]].free();

    for (auto kc : currow) {
      unsigned row = kc.first - FirstCentral;
      
      if (!Matrix[row].allocated()) { /* Insert v in Matrix at position row */
	coeff_unit_annihilator(b, a, kc.second);
	currow.mul(b);
	Matrix[row] = currow.getsparse();
	currow.clear();
	currow.addmul(a, Matrix[row]);
      
	if (Debug >= 3) {
	  fprintf(LogFile, "# Adding row %d: ",row); PrintVec(LogFile, Matrix[row]); fprintf(LogFile, "\n");
	}
      } else { /* two rows with same pivot. Merge them */
	coeff_gcdext(d, a, b, kc.second, Matrix[row][0].second); /* d = a*v[head]+b*Matrix[row][head] */
	if (!coeff_cmp(d, Matrix[row][0].second)) { /* likely case: Matrix[row][head]=d, b=1, a=0 */
	  coeff_divexact(d, kc.second, d);
	  currow.submul(d, Matrix[row]);
#ifdef COEFF_IS_MPZ // check coefficient explosion
	  if (Debug >= 1) {
	    long maxsize = 0;
	    for (coeff &c : currow)
	      maxsize = std::max(maxsize, labs(c->_mp_size));
	    fprintf(LogFile, "# Changed v: max coeff size %ld\n", maxsize);
	  }
#endif
	} else {
	  coeff_divexact(c, kc.second, d);
	  coeff_divexact(d, Matrix[row][0].second, d);
	  hollowcvec vab = vecstack.fresh();
	  vab.addmul(a, currow);
	  vab.addmul(b, Matrix[row]);
	  coeff_neg(d, d);
	  currow.mul(d);
	  currow.addmul(c, Matrix[row]);
	  Matrix[row].free();
	  Matrix[row] = vab.getsparse();
	  vecstack.pop(vab);
	  
	  if (Debug >= 3) {
	    fprintf(LogFile, "# Change row %d: ",row); PrintVec(LogFile, Matrix[row]); fprintf(LogFile, "\n");
	  }
	}
      }
    }
    vecstack.pop(currow);
  }

  coeff_clear(a);
  coeff_clear(b);
  coeff_clear(c);
  coeff_clear(d);

  TimeStamp("LU");
}

relmatrix GetRelMatrix(void) {
  LU();

  relmatrix rels;
  rels.reserve(NrCols);

  /* reduce all the head columns, to achieve Hermite normal form. */
  coeff q;
  coeff_init(q);
  for (unsigned j = 0; j < NrCols; j++) { // !!! would this be faster looping backwards?
    if (!Matrix[j].allocated())
      continue;

    hollowcvec currow = vecstack.fresh();
    currow.copysorted(Matrix[j]);
    Matrix[j].free();

    for (auto kc : currow) {
      unsigned row = kc.first - FirstCentral;
      if (row == j || !Matrix[row].allocated())
	continue;

      if (!coeff_reduced_p(kc.second, Matrix[row][0].second)) {
	coeff_fdiv_q(q, kc.second, Matrix[row][0].second);
	currow.submul(q, Matrix[row]);
      }
    }
    Matrix[j] = currow.getsparse();
    rels.push_back(Matrix[j]);
    vecstack.pop(currow);
  }

  /* !!! we could also improve this code by eliminating redundant
   generators; e.g. [2 1;0 2] could become [4 0;0 1] and allow
   elimination of the second vector. this requires a different format,
   and is perhaps best done outside this matrix code. */

  coeff_clear(q);

  TimeStamp("Hermite");
  return rels;
}

/* adds a row to the queue, and empty the queue if it got full */
void AddToRelMatrix(hollowcvec hv) {
  if (hv.empty()) // easy case: trivial relation, change nothing
    return;
  
  sparsecvec cv = hv.getsparse();
  
  if (cv[0].first < FirstCentral) // sanity check
    abortprintf(5, "AddRow: vector has a term a%d not in the centre", cv[0].first);

  auto p = Queue.insert(cv);
  if (!p.second) { // we were already there, insert failed
    cv.free();
    return;
  }

  if (Queue.size() >= 10*NrCols) // !!! adjust extra factor
    LU();
}
