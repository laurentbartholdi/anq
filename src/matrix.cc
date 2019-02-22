/******************************************************************************
**
**                 Nilpotent Quotient for Lie Rings
** matrix.c                                                     Csaba Schneider
**                                                           schcs@math.klte.hu
*/

#include "nq.h"
#include "colamd.h"
#include <algorithm>
//#include <set>
#include <unordered_set>
#include <utility>
#include <unistd.h>

/* static variables, cached from InitMatrix */
unsigned NrCols, Shift;
const coeff *TorsionExp;

/* we maintain a square NrColsxNrCols matrix (with sparse rows)
   to store the current relations. If row Matrix[i] is allocated, then
   its pivot should be in position i+Shift; so the matrix
   really has (row,column)-space equal to
   [0,NrCols) x [Shift,NrTotalGens].
*/
sparsecmat Matrix;

#ifdef HACK_to_allow_pointer_to_be_changed_in_set
// @@@ this experiment was to hack into the std::set by allowing a
// temp. to be used for searching, and then replacing it by a
// permanent copy in case the element to insert is not present.  it
// should really be done with emplace and an appropriate creator; but
// there's not much sense in doing this since the hollowcvec format is
// still much slower than the sparsevec one for vector comparison.
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

std::unordered_set<sparsecvec,hashvec<sparsecvec>,equal_tovec<sparsecvec>> Queue;

//std::set<sparsecvec,bool(*)(sparsecvec,sparsecvec)> Queue([](sparsecvec v1, sparsecvec v2){ return Compare(v1,v2) < 0; });

static void InitTorsion() {  
  if (TorsionExp != nullptr) {
    for (unsigned i = 0; i < NrCols; i++) {
      Matrix[i].alloc(1);
      Matrix[i][0].first = Shift + i;
      coeff_set(Matrix[i][0].second, *TorsionExp);
      Matrix[i].truncate(1);
    }
  }
}

void InitMatrix(const coeff *torsionexp, unsigned shift, unsigned len) {
  Shift = shift;
  NrCols = len;
  TorsionExp = torsionexp;

  Matrix.resize(NrCols, sparsecvec(nullptr));
  InitTorsion();
}

void FreeMatrix() {
  if (!Queue.empty())
    abortprintf(5, "FreeMatrix: row queue not empty");
  
  for (sparsecvec v : Matrix)
    v.free();
  Matrix.clear();
}

// for debugging purposes
void PrintMatrix() {
  for (const sparsecvec v : Matrix)
    if (v.allocated())
      PrintVec(stdout, v);
  printf("\n");
}

// try to add currow to the row space spanned by Matrix.
// return true if currow already belonged to the row space.
// currow will be damaged (well, reduced) in the process.
static bool AddRow(hollowcvec currow) {
  bool belongs = true;

  coeff a, b, c, d;
  coeff_init(a);
  coeff_init(b);
  coeff_init(c);
  coeff_init(d);

  for (auto kc : currow) {
    unsigned row = kc.first - Shift;
      
    if (!Matrix[row].allocated()) { /* Insert v in Matrix at position row */
      belongs = false;
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
      if (!coeff_cmp(d, Matrix[row][0].second)) { /* likely case: Matrix[row][head]=d, b=1, a=0. We're just reducing currow. */
	coeff_divexact(d, kc.second, d);
	currow.submul(d, Matrix[row]);
#ifdef COEFF_IS_MPZ // check coefficient explosion
	if (Debug >= 1) {
	  long maxsize = 0;
	  for (auto kc : currow)
	    maxsize = std::max(maxsize, labs(kc.second->_mp_size));
	  fprintf(LogFile, "# Changed currow: max coeff size %ld\n", maxsize);
	}
#endif
      } else {
	belongs = false;
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

  coeff_clear(a);
  coeff_clear(b);
  coeff_clear(c);
  coeff_clear(d);

  return belongs;
}

bool AddToMatrix(hollowcvec currow) {
  if (currow.empty())
    return true;
  if (currow.front()->first < Shift)
    abortprintf(5, "AddToMatrix: vector has a term a%d of too low index", currow.front()->first);
  return AddRow(currow);
}

  std::vector<int> colamd(sparsecmat &m) {
  std::vector<int> ind;
  int stats[COLAMD_STATS];
  std::vector<int> intmat;

  for (const sparsecvec v : m) {
    ind.push_back(intmat.size());
    for (auto kc : v)
      intmat.push_back(kc.first - Shift);
  }
  ind.push_back(intmat.size());

  if (Debug >= 2) {
    fprintf(LogFile, "# about to collect %ld relations (%ld nnz)\n", m.size(), intmat.size());
  }

  size_t alloc = colamd_recommended(intmat.size(), NrCols, m.size());
  intmat.reserve(alloc);
  int ok = colamd(NrCols, m.size(), alloc, intmat.data(), ind.data(), NULL, stats);
  if (Debug >= 3) {
    // we capture the output of colamd_report, and pipe it to LogFile.
    // strangely enough, the documentation says that colamd_report writes to
    // stderr, but it seems that it writes, rather, to stdout.

    int fds[2], oldstdout;

    pipe(fds);
    oldstdout = dup(STDOUT_FILENO);
    dup2(fds[1], STDOUT_FILENO);

    colamd_report(stats);
    fprintf(stdout, "$\n"); // end
    fflush(stdout);

    dup2(oldstdout, STDOUT_FILENO);

    { // ideally, we would fork() in a child who does the printing.
      // the output is short enough that there's no trouble doing it
      // here: pipe(2) should guarantee 64k of buffering.
      char c;
      bool begin = true;
      while (read(fds[0],&c,1) == 1) {
	if (c == '$')
	  break;
	fprintf(LogFile, "%s%c", begin ? "# " : "", c);
	begin = (c == '\n');
      }
    }

    close(fds[0]);
    close(fds[1]);
    
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
void FlushMatrixQueue() {
  if (Queue.empty())
    return;
  
  /* remove unbound entries in Matrix */
  Matrix.erase(std::remove(Matrix.begin(), Matrix.end(), sparsecvec(nullptr)), Matrix.end());

  /* put queue at bottom of matrix */
  Matrix.insert(Matrix.end(), Queue.begin(), Queue.end());  
  Queue.clear();

  /* call colamd to determine optimal insertion ordering */
  std::vector<int> ind = colamd(Matrix);
  
  sparsecmat oldrels(NrCols, sparsecvec(nullptr));
  Matrix.swap(oldrels);
  InitTorsion();

  /* add rows of oldrels into Matrix, reducing them along the way, and in
     the order specified by the permutation ind */
  for (unsigned i = 0; i < oldrels.size(); i++) {
    hollowcvec currow = vecstack.fresh();
    currow.copysorted(oldrels[ind[i]]);
    oldrels[ind[i]].free();
    AddRow(currow);
    vecstack.pop(currow);
  }

  TimeStamp("FlushMatrixQueue()");
}

sparsecmat GetMatrix() {
  FlushMatrixQueue();

  sparsecmat rels;
  rels.reserve(NrCols);

  /* reduce all the head columns, to achieve Hermite normal form. */
  coeff q;
  coeff_init(q);
  for (unsigned j = 0; j < NrCols; j++) { // @@@ performance: would this be faster looping backwards?
    if (!Matrix[j].allocated())
      continue;

    hollowcvec currow = vecstack.fresh();
    currow.copysorted(Matrix[j]);
    Matrix[j].free();

    for (auto kc : currow) {
      unsigned row = kc.first - Shift;
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

  /* @@@ We could improve this code by eliminating redundant
   generators; e.g. [2 1;0 2] could become [4 0;2 1] and allow
   elimination of the second vector, after permuting the first and
   second columns. This requires a different format, and is perhaps
   best done outside this matrix code. */

  coeff_clear(q);

  TimeStamp("Hermite()");
  return rels;
}

/* tries to add a row to the queue; returns true if the row was added.
 empty the queue if it got full. */
void QueueInMatrix(hollowcvec hv) {
  if (hv.empty()) // easy case: trivial relation, change nothing
    return;

  // @@@ performance critical: maybe we can avoid making a copy?
  sparsecvec cv = hv.getsparse();

  if (cv[0].first < Shift) // sanity check
    abortprintf(5, "QueueInMatrix: vector has a term a%d of too low index", cv[0].first);

  auto p = Queue.insert(cv);
  if (!p.second) { // we were already there, insert failed
    cv.free();
    return;
  }

  /* @@@ optimize for the factor "10". If too small, we'll cause
     fill-in in the matrix. If too large, we'll use too much
     memory. */
  if (Queue.size() >= 10*NrCols)
    FlushMatrixQueue();
}
