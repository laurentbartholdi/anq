/******************************************************************************
**
**                 Nilpotent Quotient for Lie Rings
** matrix.c                                                     Csaba Schneider
**                                                           schcs@math.klte.hu
*/

#include "nq.h"
#include "colamd.h"
#include <algorithm>
#include <utility>
#include <unistd.h>

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

matrix::matrix(unsigned _nrcols, unsigned _shift, bool _torsionfree) : nrcols(_nrcols), shift(_shift), torsionfree(_torsionfree) {
  rows.resize(nrcols, sparsematvec::null());
  rowstack.setsize(nrcols);
}

matrix::~matrix() {
  if (!queue.empty())
    abortprintf(5, "matrix::~matrix: row queue not empty");

  for (sparsematvec v : rows)
    v.free();
  rows.clear();
}

// put v in normal form by subtracting rows of Matrix, return in fresh vector
// !!! this is time-critical. Optimize!
sparsepcvec matrix::reducerow(const sparsepcvec &v) const {
  matcoeff q;
  q.init();
  hollowmatvec hv = rowstack.fresh();

  for (auto &kc : v)
    map(hv[kc.first-shift], kc.second);

  for (const auto &kc : hv) {
    unsigned row = kc.first;

    if (rows[row].allocated() && !reduced_p(kc.second, rows[row][0].second)) { // found a pivot
      shdiv_q(q, kc.second, rows[row][0].second);
      hv.submul(q, rows[row]);
    }
  }

  sparsepcvec r;
  r.alloc(hv.size());

  auto ri = r.begin();
  for (const auto &kc : hv) {
    ri->first = kc.first+shift;
    map(ri->second, kc.second);
    ri++;
  }
  ri.markend();

  rowstack.release(hv);
  q.clear();

  return r;
}

// try to add currow to the row space spanned by rows.
// return true if currow already belonged to the row space.
// currow will be damaged (well, reduced) in the process.
bool matrix::add1row(hollowmatvec currow) {
  bool belongs = true;

  matcoeff a, b, c, d;
  a.init();
  b.init();
  c.init();
  d.init();

  for (const auto &kc : currow) {
    unsigned row = kc.first;

    if (!rows[row].allocated()) { /* Insert v in rows at position row */
      belongs = false;
      unit_annihilator(&b, &a, kc.second);
      currow.scale(b);
      rows[row] = currow.getsparse();
      currow.clear();
      currow.addmul(a, rows[row]);

      if (Debug >= 3)
	fprintf(LogFile, "# Adding row %d: " PRIsparsematvec "\n", row, &rows[row]);
    } else { /* two rows with same pivot. Merge them */
      gcdext(d, a, b, kc.second, rows[row][0].second); /* d = a*v[head]+b*rows[row][head] */
      if (!cmp(d,rows[row][0].second)) { /* likely case: rows[row][head]=d. We're just reducing currow. */
	shdivexact(d, kc.second, d);
	currow.submul(d, rows[row]);
#ifdef IS_MPZ // check coefficient explosion
	if (Debug >= 1) {
	  long maxsize = 0;
	  for (const auto &kc : currow)
	    maxsize = std::max(maxsize, labs(kc.second->_mp_size));
	  fprintf(LogFile, "# Changed currow: max coeff size %ld\n", maxsize);
	}
#endif
      } else {
	belongs = false;
	shdivexact(c, kc.second, d);
	shdivexact(d, rows[row][0].second, d);
	hollowmatvec vab = rowstack.fresh();
	vab.addmul(a, currow);
	vab.addmul(b, rows[row]);
	neg(d, d);
	currow.scale(d);
	currow.addmul(c, rows[row]);
	rows[row].free();
	rows[row] = vab.getsparse();
	rowstack.release(vab);

	if (Debug >= 3)
	  fprintf(LogFile, "# Change row %d: " PRIsparsematvec "\n", row, &rows[row]);

	if (rows[row].begin()->first != row)
	  abortprintf(5, "add1row created a row with pivot at wrong coordinate");
	unit_annihilator(&a, nullptr, rows[row].begin()->second);
	if (cmp_si(a, 1))
	  abortprintf(5, "add1row created a non-normalized row");
      }
    }
  }

  d.clear();
  c.clear();
  b.clear();
  a.clear();

  return belongs;
}

bool matrix::addrow(hollowpcvec currow) {
  if (currow.empty())
    return true;
  if (currow.begin()->first < shift)
    abortprintf(5, "matrix::addrow: vector has a term a%d of too low index", currow.begin()->first);

  hollowmatvec row = rowstack.fresh();
  for (const auto &kc : currow)
    map(row[kc.first-shift], kc.second);

  bool status = add1row(row);
  rowstack.release(row);
  return status;
}

static std::vector<int> colamd(sparsematmat &m, unsigned nrcols) {
  std::vector<int> ind;
  int stats[COLAMD_STATS];
  std::vector<int> intmat;

  for (const sparsematvec v : m) {
    ind.push_back(intmat.size());
    for (const auto &kc : v)
      intmat.push_back(kc.first);
  }
  ind.push_back(intmat.size());

  if (Debug >= 2) {
    fprintf(LogFile, "# about to collect %ld relations (%ld nnz)\n", m.size(), intmat.size());
    fprintf(LogFile, "# ind:");
    for (unsigned i = 0; i < ind.size(); i++) fprintf(LogFile, " %d", ind[i]);
    fprintf(LogFile, "\n# intmat:");
    for (unsigned i = 0; i < intmat.size(); i++) fprintf(LogFile, " %d", intmat[i]);
    fprintf(LogFile, "\n");
  }

  size_t alloc = colamd_recommended(intmat.size(), nrcols, m.size());
  intmat.reserve(alloc);
  int ok = colamd(nrcols, m.size(), alloc, intmat.data(), ind.data(), NULL, stats);
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

/* collect the vectors in queue and Matrix, and combine them back into Matrix */
void matrix::flushqueue() {
  if (queue.empty())
    return;

  /* remove unbound entries in rows */
  rows.erase(std::remove(rows.begin(), rows.end(), sparsematvec::null()), rows.end());

  /* put queue at bottom of matrix */
  rows.insert(rows.end(), queue.begin(), queue.end());
  queue.clear();

  /* call colamd to determine optimal insertion ordering */
  std::vector<int> ind = colamd(rows, nrcols);

  sparsematmat oldrels(nrcols, sparsematvec::null());
  rows.swap(oldrels);

  /* add rows of oldrels into rows, reducing them along the way, and in
     the order specified by the permutation ind */
  for (unsigned i = 0; i < oldrels.size(); i++) {
    hollowmatvec currow = rowstack.fresh();
    currow.copy(oldrels[ind[i]]);
    oldrels[ind[i]].free();
    add1row(currow);
    rowstack.release(currow);
  }
  TimeStamp("matrix::flushqueue()");
}

// @@@ find tricks to avoid arithmetic overflow

// complete the Hermite normal form
void matrix::hermite() {
  /* reduce all the head columns, to achieve Hermite normal form. */
  matcoeff q;
  q.init();
  for (int j = nrcols-1; j >= 0; j--) {
    if (!rows[j].allocated())
      continue;

    hollowmatvec currow = rowstack.fresh();
    currow.copy(rows[j]);
    rows[j].free();

    for (const auto &kc : currow) {
      unsigned row = kc.first;
      if (row == (unsigned) j || !rows[row].allocated())
	continue;

      if (!reduced_p(kc.second, rows[row][0].second)) {
	shdiv_q(q, kc.second, rows[row][0].second);
	currow.submul(q, rows[row]);
      }
    }

    if (torsionfree) { // furthermore, divide by gcd of row entries
      matcoeff gcd, a, b;
      gcd.init();
      a.init();
      b.init();
      gcd.set_si(0);
      for (const auto &kc : currow) {
	gcdext(gcd, a, b, kc.second, gcd);
	if (!gcd.cmp_si(1))
	  goto stop;
      }
      for (const auto &kc : currow)
	shdivexact(kc.second, kc.second, gcd);
    stop:
      b.clear();
      a.clear();
      gcd.clear();
    }

    rows[j] = currow.getsparse();
    rowstack.release(currow);
  }

  /* @@@ We could improve this code by eliminating redundant
   generators; e.g. [2 1;0 2] could become [4 0;2 1] and allow
   elimination of the second vector, after permuting the first and
   second columns. This requires a different format, and is perhaps
   best done outside this matrix code. */

  q.clear();

  TimeStamp("matrix::hermite()");
}

// return relator
sparsepcvec matrix::getrel(pccoeff &c, gen g) const {
  const auto row = rows[g-shift];
  matcoeff q;
  q.init();
  sparsepcvec v;

  if (row.allocated()) {
    v.alloc(row.size()-1);
    auto vi = v.begin();
    auto rowi = row.begin();
    map(c, rowi->second);
    for (++rowi; rowi != row.end(); ++rowi) {
      q.neg(rowi->second);
      map(vi->second, q);
      vi->first = rowi->first+shift;
      vi++;
    }
    vi.markend();
  } else {
    v.noalloc();
    c.kernel<matcoeff>();
  }
  q.clear();
  return v;
}

/* tries to add a row to the queue; returns true if the row was added.
 empty the queue if it got full. */
void matrix::queuerow(const hollowpcvec hv) {
  if (hv.empty()) // easy case: trivial relation, change nothing
    return;

  sparsematvec cv;
  {
    cv.alloc(hv.size());
    auto i = cv.begin();
    for (const auto &kc : hv) {
      i->second.map(kc.second);
      if (kc.first < shift) // sanity check
	abortprintf(5, "matrix::queuerow: vector has a term a%d of too low index", cv[0].first);
      i->first = kc.first-shift;
      i++;
    }
    i.markend();
  }

  auto p = queue.insert(cv);
  if (!p.second) { // we were already there, insert failed
    cv.free();
    return;
  }

  /* @@@ optimize for the factor "10". If too small, we'll cause
     fill-in in the matrix. If too large, we'll use too much
     memory. */
  if (queue.size() >= 10*nrcols)
    flushqueue();
}
