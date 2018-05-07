/******************************************************************************
**
**                 Nilpotent Quotient for Lie Rings
** matrix.c                                                     Csaba Schneider
**                                                           schcs@math.klte.hu
*/

#include "lienq.h"
#include "colamd.h"
#include <algorithm>
#include <set>
#include <utility>

/* static variables, cached from InitMatrix */
unsigned NrCols, FirstCentral;
bool Torsion;
const coeff *TorsionExp;

// y += a*x. scratch is available as temporary storage.
// this routine takes 80% of the runtime! optimize generously.
inline void SAXPY(gpvec y, coeff &a, constgpvec x, gpvec scratch)
{
  if (coeff_z_p(a))
    return;

  /* initially, we follow y and try to add a*x to it.

     if we're out of space, then we copy the remainder of y to
     scratch, and add from scratch and a*x into y.

     if on the contrary we got an extra cancellation, we keep track of
     yin and yout */

  while (x->g != EOW) {
    while (y->g < x->g) y++;
    if (y->g == x->g) {
      coeff_addmul(y->c, a, x->c);
      x++;
      if (coeff_z_p(y->c)) { // extra cancellation
	gpvec yout = y++;
	while (yout < y) {
	  if (x->g == EOW) {
	    Copy(yout, y);
	    return;
	  }
	  while (y->g < x->g) {
	    coeff_set(yout->c, y->c);
	    (yout++)->g = (y++)->g;
	  }
	  if (y->g == x->g) {
	    coeff_set(yout->c, y->c);
	    coeff_addmul(yout->c, a, x->c);
	    if (coeff_nz_p(yout->c))
	      (yout++)->g = y->g;
	    y++;
	    x++;
	  } else {
	    coeff_mul(yout->c, a, x->c);
	    if (coeff_nz_p(yout->c))
	      (yout++)->g = x->g;
	    x++;
	  }
	}
      } else
	y++;
    } else {
      Copy(scratch, y);
      Sum(y, scratch, a, x);
      return;
    }
  }
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
      Matrix[i][0].g = FirstCentral + i;
      coeff_set(Matrix[i][0].c, *TorsionExp);
      Matrix[i][1].g = EOW;
    }
  }
}

void InitRelMatrix(const pcpresentation &pc, unsigned nrcentralgens) {
  FirstCentral = pc.NrPcGens + 1;
  NrCols = nrcentralgens;
  Torsion = pc.PAlgebra;
  TorsionExp = &pc.TorsionExp;

  Matrix.resize(NrCols, NULL);
  InitTorsion();
}

void FreeRelMatrix(void) {
  if (!Queue.empty())
    abortprintf(5, "FreeMatrix: row queue not empty");
  
  for (gpvec v : Matrix)
    if (v)
      FreeVec(v, NrCols);
  Matrix.clear();
}

// for debugging purposes
void PrintMatrix(void) {
  for (constgpvec v : Matrix)
    if (v)
      PrintVec(stdout, v);
  printf("\n");
}
    
/* collect the vectors in Queue and Matrix, and combine them back into Matrix */
void LU(void) {
  /* remove unbound entries in Matrix */
  Matrix.erase(std::remove(Matrix.begin(), Matrix.end(), (gpvec) 0), Matrix.end());

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
      for (constgpvec w = v; w->g != EOW; w++)
	intmat.push_back(w->g - FirstCentral);
    }
    ind.push_back(intmat.size());

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
  
  std::vector<gpvec> oldrels(NrCols, NULL);
  Matrix.swap(oldrels);
  InitTorsion();

  gpvec scratch[3] = { NewVec(NrCols), NewVec(NrCols), NewVec(NrCols) };
  coeff a, b, c, d;
  coeff_init(a);
  coeff_init(b);
  coeff_init(c);
  coeff_init(d);

  /* add rows of oldrels into Matrix, reducing them along the way, and in
     the order specified by the permutation ind */
  for (unsigned i = 0; i < oldrels.size(); i++) {
    {
      gpvec v = oldrels[ind[i]];
      Copy(scratch[0], v);
      FreeVec(v);
    }
    
    while (scratch[0]->g != EOW) {
      unsigned row = scratch[0]->g - FirstCentral;
      
      if (Matrix[row] == NULL) { /* Insert v in Matrix at position row */
	coeff_unit_annihilator(b, a, scratch[0]->c);
	Matrix[row] = NewVec(NrCols);
	Prod(Matrix[row], b, scratch[0]);
	Prod(scratch[0], a, scratch[0]);
      
	if (Debug >= 3) {
	  fprintf(LogFile, "# Adding row %d: ",row); PrintVec(LogFile, Matrix[row]); fprintf(LogFile, "\n");
	}
      } else { /* two rows with same pivot. Merge them */
	coeff_gcdext(d, a, b, scratch[0]->c, Matrix[row]->c); /* d = a*v[head]+b*Matrix[row][head] */
	if (!coeff_cmp(d, Matrix[row]->c)) { /* likely case: Matrix[row][head]=d, b=1, a=0 */
	  coeff_divexact(d, scratch[0]->c, d);
	  coeff_neg(d, d);
	  SAXPY(scratch[0], d, Matrix[row], scratch[1]);
#ifdef COEFF_IS_MPZ // check coefficient explosion
	  if (Debug >= 1) {
	    long maxsize = 0;
	    for (gpvec q = scratch[0]; q->g != EOW; q++)
	      maxsize = std::max(maxsize, labs(q->c->_mp_size));
	    fprintf(LogFile, "# Changed v: max coeff size %ld\n", maxsize);
	  }
#endif
	} else {
	  coeff_divexact(c, scratch[0]->c, d);
	  coeff_divexact(d, Matrix[row]->c, d);
	  Sum(scratch[1], a, scratch[0], b, Matrix[row]);
	  Diff(scratch[2], c, Matrix[row], d, scratch[0]);
	  std::swap(Matrix[row], scratch[1]);
	  std::swap(scratch[0], scratch[2]);

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
  for (gpvec v : scratch) FreeVec(v);

  TimeStamp("LU");
}

relmatrix GetRelMatrix(void) {
  LU();

  /* reduce all the head columns, to achieve Hermite normal form. */
  {
    gpvec scratch = NewVec(NrCols);
    coeff q;
    coeff_init(q);
    for (gpvec &v : Matrix) { // !!! would this be faster looping backwards?
      if (!v)
	continue;

      for (unsigned i = 1; v[i].g != EOW;) {
	gpvec w = Matrix[v[i].g - FirstCentral];
	if (!w)
	  goto skip;
	
	coeff_fdiv_q(q, v[i].c, w->c);
	if (coeff_nz_p(q)) {
	  Diff(scratch, v, q, w); // !!! could only subtract from position v[i]
	  std::swap(v, scratch);
	  continue;
	}
      skip:
	i++;
      }
    }
    coeff_clear(q);
    FreeVec(scratch);
  }
  TimeStamp("Hermite");

  relmatrix rels;
  rels.reserve(NrCols);
  for (constgpvec v : Matrix)
    if (v != NULL)
      rels.push_back(v);
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
