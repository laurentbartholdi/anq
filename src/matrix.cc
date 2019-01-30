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

typedef std::vector<coeff> coeffvec;

inline coeffvec NEW(unsigned length)
{
  coeffvec v(length);
  for (unsigned i = 0; i < length; i++)
    coeff_init_set_si(v[i], 0);
  return v;
}

inline void FREE(coeffvec &v)
{
  for (coeff &c : v)
    coeff_clear(c);
}

inline gpvec GET(coeffvec &v)
{
  unsigned len = 0;
  for (coeff &c : v)
    if (coeff_nz_p(c))
      len++;
  gpvec r = NewVec(len), p = r;
  for (unsigned i = 0; i < v.size(); i++) {
    if (coeff_z_p(v[i]))
      continue;
    p->g = i + FirstCentral;
    coeff_set(p->c, v[i]);
    coeff_zero(v[i]);
    p++;
  }
  p->g = EOW;
  return r;
}

inline gpvec GET(coeffvec &v, coeff &a)
{
  unsigned len = 0;
  gpvec r = NewVec(v.size()), p = r;
  for (unsigned i = 0; i < v.size(); i++) {
    p->g = i + FirstCentral;
    coeff_mul(p->c, v[i], a);
    coeff_zero(v[i]);
    if (coeff_nz_p(p->c))
      p++, len++;
  }
  p->g = EOW;
  return ResizeVec(r, v.size(), len);
}

inline void CX(constgpvec x, coeffvec &y)
{
  for (auto gc: x)
    coeff_set(y[gc.g - FirstCentral], gc.c);
}

inline void CAX(const coeff &a, constgpvec x, coeffvec &y)
{
  for (auto gc: x)
    coeff_mul(y[gc.g - FirstCentral], a, gc.c);
}

inline void CAXPY(const coeff &a, constgpvec x, coeffvec &y)
{
  for (auto gc: x)
    coeff_addmul(y[gc.g - FirstCentral], a, gc.c);
}

inline void CAXPBYZ(const coeff &a, const coeffvec &x, const coeff &b, constgpvec y, coeffvec &z)
{
  for (unsigned i = 0; i < x.size(); i++)
    coeff_mul(z[i], a, x[i]);
  CAXPY(b, y, z);
}

std::vector<gpvec> Matrix;
#ifdef CUSTOM_ALLOC
template<typename T> struct gpvec_allocator: public std::allocator<T>
{
  template<class U> struct rebind { typedef gpvec_allocator<U> other; };
  typedef std::allocator<T> base;
  typename base::pointer allocate(typename base::size_type n) {
    fprintf(stderr,"ALLOC %d",n); // here we want to make a copy
    return this->base::allocate(n);
  }
  typename base::pointer allocate(typename base::size_type n, void const* hint) {
    fprintf(stderr,"ALLOC %d",n);
    return this->base::allocate(n, hint);
  }
};
std::set<gpvec,bool(*)(gpvec,gpvec),gpvec_allocator<gpvec>> Queue([](gpvec v1, gpvec v2){ return Compare(v1,v2) < 0; });
#else
// hack to allow pointer to be changed in set
struct __gpvec { mutable gpvec v; };
std::set<__gpvec,bool(*)(__gpvec,__gpvec)> Queue([](__gpvec v1, __gpvec v2){ return Compare(v1.v,v2.v) < 0; });
#endif

static void InitTorsion(void) {  
  if (Torsion) {
    for (unsigned i = 0; i < NrCols; i++) {
      Matrix[i] = NewVec(1);
      Matrix[i]->g = FirstCentral + i;
      coeff_set(Matrix[i]->c, *TorsionExp);
      (Matrix[i]+1)->g = EOW;
    }
  }
}

void InitRelMatrix(const pcpresentation &pc, unsigned nrcentralgens) {
  FirstCentral = pc.NrPcGens + 1;
  NrCols = nrcentralgens;
  Torsion = pc.PAlgebra;
  TorsionExp = &pc.TorsionExp;

  Matrix.resize(NrCols, nullgpvec);
  InitTorsion();
}

void FreeRelMatrix(void) {
  if (!Queue.empty())
    abortprintf(5, "FreeMatrix: row queue not empty");
  
  for (gpvec v : Matrix)
    if (v != nullgpvec)
      FreeVec(v, NrCols);
  Matrix.clear();
}

// for debugging purposes
void PrintMatrix(void) {
  for (constgpvec v : Matrix)
    if (v != nullgpvec)
      PrintVec(stdout, v);
  printf("\n");
}
    
/* collect the vectors in Queue and Matrix, and combine them back into Matrix */
void LU(void) {
  /* remove unbound entries in Matrix */
  Matrix.erase(std::remove(Matrix.begin(), Matrix.end(), nullgpvec), Matrix.end());

  /* put queue at bottom of matrix */
#ifdef CUSTOM_ALLOC
  Matrix.insert(Matrix.end(), Queue.begin(), Queue.end());
#else
  std::transform(Queue.begin(), Queue.end(), std::back_inserter(Matrix), [](__gpvec v) { return v.v; });
#endif
  
  Queue.clear();

  /* call colamd to determine optimal insertion ordering */
  std::vector<int> ind;
  {
    int stats[COLAMD_STATS];
    std::vector<int> intmat;
    for (constgpvec v : Matrix) {
      ind.push_back(intmat.size());
      for (auto gc: v)
	intmat.push_back(gc.g - FirstCentral);
    }
    ind.push_back(intmat.size());

    if (Debug >= 2) {
      fprintf(LogFile, "# about to collect %ld relations (%ld nnz)\n", Matrix.size(), intmat.size());
    }

    size_t alloc = colamd_recommended(intmat.size(), NrCols, Matrix.size());
    intmat.reserve(alloc);
    int ok = colamd(NrCols, Matrix.size(), alloc, intmat.data(), ind.data(), NULL, stats);
    if (Debug >= 3) {
      colamd_report(stats);
      fprintf(LogFile, "# row permutation:");
      for (unsigned i = 0; i < Matrix.size(); i++)
	fprintf(LogFile, " %u", ind[i]);
      fprintf(LogFile,"\n");
    }
      
    if (!ok)
      abortprintf(5, "colamd error %d", ok);
  }
  
  std::vector<gpvec> oldrels(NrCols, nullgpvec);
  Matrix.swap(oldrels);
  InitTorsion();

  coeffvec newrow = NEW(NrCols), scratch = NEW(NrCols);
  coeff a, b, c, d;
  coeff_init(a);
  coeff_init(b);
  coeff_init(c);
  coeff_init(d);

  /* add rows of oldrels into Matrix, reducing them along the way, and in
     the order specified by the permutation ind */
  for (unsigned i = 0; i < oldrels.size(); i++) {
    CX(oldrels[ind[i]], newrow);
    FreeVec(oldrels[ind[i]]);

    for (unsigned row = 0; row < NrCols; row++) {
      if (coeff_z_p(newrow[row]))
	continue;
      
      if (Matrix[row] == nullgpvec) { /* Insert v in Matrix at position row */
	coeff_unit_annihilator(b, a, newrow[row]);
	Matrix[row] = GET(newrow, b);
	CAX(a, Matrix[row], newrow);
      
	if (Debug >= 3) {
	  fprintf(LogFile, "# Adding row %d: ",row); PrintVec(LogFile, Matrix[row]); fprintf(LogFile, "\n");
	}
      } else { /* two rows with same pivot. Merge them */
	coeff_gcdext(d, a, b, newrow[row], Matrix[row]->c); /* d = a*v[head]+b*Matrix[row][head] */
	if (!coeff_cmp(d, Matrix[row]->c)) { /* likely case: Matrix[row][head]=d, b=1, a=0 */
	  coeff_divexact(d, newrow[row], d);
	  coeff_neg(d, d);
	  CAXPY(d, Matrix[row], newrow);
#ifdef COEFF_IS_MPZ // check coefficient explosion
	  if (Debug >= 1) {
	    long maxsize = 0;
	    for (coeff &c : newrow)
	      maxsize = std::max(maxsize, labs(c->_mp_size));
	    fprintf(LogFile, "# Changed v: max coeff size %ld\n", maxsize);
	  }
#endif
	} else {
	  coeff_divexact(c, newrow[row], d);
	  coeff_divexact(d, Matrix[row]->c, d);
	  CAXPBYZ(a, newrow, b, Matrix[row], scratch);
	  coeff_neg(d, d);
	  CAXPBYZ(d, newrow, c, Matrix[row], newrow);
	  FreeVec(Matrix[row]);
	  Matrix[row] = GET(scratch);

	  if (Debug >= 3) {
	    fprintf(LogFile, "# Change row %d: ",row); PrintVec(LogFile, Matrix[row]); fprintf(LogFile, "\n");
	  }
	}
      }
    }
  }

  coeff_clear(a);
  coeff_clear(b);
  coeff_clear(c);
  coeff_clear(d);
  FREE(newrow);
  FREE(scratch);

  TimeStamp("LU");
}

relmatrix GetRelMatrix(void) {
  LU();

  relmatrix rels;
  rels.reserve(NrCols);

  /* reduce all the head columns, to achieve Hermite normal form. */
  coeffvec newrow = NEW(NrCols);
  coeff q;
  coeff_init(q);
  for (unsigned j = 0; j < NrCols; j++) { // !!! would this be faster looping backwards?
    if (Matrix[j] == nullgpvec)
      continue;
    CX(Matrix[j], newrow);
    FreeVec(Matrix[j]);

    for (unsigned i = j+1; i < NrCols; i++) {
      gpvec w = Matrix[i];
      if (w == nullgpvec)
	continue;

      if (!coeff_reduced_p(newrow[i], w->c)) {
	coeff_fdiv_q(q, newrow[i], w->c);
	coeff_neg(q, q);
	CAXPY(q, w, newrow);
      }
    }
    Matrix[j] = GET(newrow);
    rels.push_back(Matrix[j]);
  }

  /* !!! we could also improve this code by eliminating redundant
   generators; e.g. [2 1;0 2] could become [4 0;0 1] and allow
   elimination of the second vector. this requires a different format,
   and is perhaps best done outside this matrix code. */

  coeff_clear(q);
  FREE(newrow);

  TimeStamp("Hermite");
  return rels;
}

/* adds a row to the queue, and empty the queue if it got full */
void AddToRelMatrix(gpvec cv) {
  if (cv->g == EOW) // easy case: trivial relation, change nothing
    return;
  
  if (cv->g < FirstCentral) // sanity check
    abortprintf(5, "AddRow: vector has a term a%d not in the centre", cv->g);

#ifdef CUSTOM_ALLOC
  auto p = Queue.emplace(cv);
#else
  __gpvec xv = {.v = cv};
  auto p = Queue.emplace(xv);

  if (p.second) // make the copy permanent
    Copy(p.first->v = NewVec(Length(cv)), cv);
#endif
  
  if (!p.second)
    return;

  if (Queue.size() >= 10*NrCols) // !!! adjust extra factor
    LU();
}
