/****************************************************************
 * compute row echelon form of matrix over finite ring Z/n.
 * based on linbox.
 ****************************************************************/

#include "rref.h"

constexpr inline uint64_t powint(uint64_t x, uint64_t p) {
  return p ? (p & 1 ? x : 1)*powint(x*x, p>>1) : 1;
}

#ifdef USE_LINBOX // seems broken

#include <linbox/linbox-config.h>
#include <linbox/matrix/sparse-matrix.h>
#include <linbox/algorithms/smith-form-sparseelim-poweroftwo.h>
#include <givaro/modular.h>
#include <linbox/algorithms/smith-form-sparseelim-local.h>

template<class T, class ring_t> std::pair<std::vector<T>, sparse_mat<T>> cleanup(std::vector<std::pair<size_t,uint64_t>> _S, LinBox::SparseMatrix<ring_t,LinBox::SparseMatrixFormat::SparseSeq> A, LinBox::Permutation<ring_t> _Q) {
  std::vector<uint64_t> S, Q;

  for (auto p: _S)
    for (unsigned i = 0; i < p.first; i++)
      S.push_back(p.second);

  Q.reserve(A.coldim());
  for (auto p: _Q.getStorage())
    Q.push_back(p);

  std::vector<T> pivots;
  sparse_mat<T> reduced;
  size_t nr_rows = 0;
  
  for (auto row: A.refRep())
    if (!row.empty()) {
      for (auto col: row)
	reduced(nr_rows,Q[col.first]) = S[nr_rows] * col.second;
      pivots.push_back(Q[row[0].first]);
      nr_rows++;
    }

  // debug!!!
  std::cout << "S: " << S << std::endl;
  std::cout << "A: "; A.write(std::cout,LinBox::Tag::FileFormat::Maple) << std::endl;
  std::cout << "Q: " << Q << std::endl;
  
  return std::pair<std::vector<T>,sparse_mat<T>>(pivots,reduced);
}

template<class T> std::pair<std::vector<T>,sparse_mat<T>> sparse_mat<T>::rref(size_t p, size_t e) {
  LinBox::commentator().setMaxDetailLevel (-1);
  LinBox::commentator().setMaxDepth (-1);
  LinBox::commentator().setReportStream (std::cerr);

  size_t modulus = powint(p,e);
  std::vector<std::pair<size_t,uint64_t>> S;

  if (p == 2) {
    typedef Givaro::ZRing<uint64_t> ring_t;
    ring_t R;
    LinBox::PowerGaussDomainPowerOfTwo<uint64_t> PGD;
    LinBox::SparseMatrix<ring_t,LinBox::SparseMatrixFormat::SparseSeq> A(R);
    A.resize(rows(),nrcols);
    for (auto row: mat)
      for (auto col: row.second)
	A.setEntry(row.first, col.first, col.second & (modulus-1));
    LinBox::Permutation<ring_t> Q(R,nrcols);
    PGD(S, A, Q, e, LinBox::PRESERVE_UPPER_MATRIX | LinBox::PRIVILEGIATE_NO_COLUMN_PIVOTING);
    return cleanup<T,ring_t>(S, A, Q);
  } else {
    typedef Givaro::Modular<uint64_t> ring_t;
    ring_t R(modulus);
    LinBox::PowerGaussDomain<ring_t> PGD(R);
    LinBox::SparseMatrix<ring_t,LinBox::SparseMatrixFormat::SparseSeq> A(R);
    A.resize(rows(),nrcols);
    for (auto row: mat)
      for (auto col: row.second) {
	T v = col.second % modulus;
	if (v < 0) v += modulus;
	A.setEntry(row.first, col.first, v);
      }
    LinBox::Permutation<ring_t> Q(R,nrcols);
    PGD(S, A, Q, (unsigned long long) modulus, (unsigned long long) p, LinBox::PRESERVE_UPPER_MATRIX | LinBox::PRIVILEGIATE_NO_COLUMN_PIVOTING | LinBox::PRIVILEGIATE_REDUCING_FILLIN);
    return cleanup<T,ring_t>(S, A, Q);
  }
}

#elif defined(USE_NTL)

#include <NTL/ZZ.h>
//#include <NTL/matrix.h>
#include <NTL/mat_ZZ.h>
#include <NTL/HNF.h>

template<class T> std::pair<std::vector<T>,sparse_mat<T>> sparse_mat<T>::rref(size_t p, size_t e) {

  NTL::mat_ZZ A, hnf;
  NTL::ZZ det{(long) powint(p,e)};
  A.SetDims(nrrows, nrcols);
  hnf.SetDims(nrcols, nrcols);
  
  for (auto row: mat)
    for (auto col: row.second)
      A(row.first+1,col.first+1) = col.second;

  NTL::HNF(hnf, A, det);

  size_t nrrows = hnf.NumRows(), nrcols = hnf.NumCols();
  
  std::vector<T> pivots;
  sparse_mat<T> reduced;

  for (size_t i = 1; i <= nrrows; i++)
    for (size_t j = 1; j <= nrcols; j++)
      reduced(i-1,j-1) = to_long(hnf(i,j));
  
  return std::pair<std::vector<T>,sparse_mat<T>>(pivots,reduced);

}

#else // USE_FLINT

#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/fmpz_mat.h>

template<class T> sparse_mat<T> sparse_mat<T>::nullspace(void) {
  fmpz_mat_t A;
  fmpz_mat_init(A, nrcols, nrrows + nrcols);
  
  for (auto row: mat)
    for (auto col: row.second)
      fmpz_set_si(fmpz_mat_entry(A,col.first,row.first), col.second);
  for (size_t c = 0; c < nrcols; c++)
    fmpz_set_si(fmpz_mat_entry(A,c,nrrows+c), 1);
  
  fmpz_mat_hnf(A, A);

  sparse_mat<T> result;
  size_t nullity = 0;
  
  for (size_t i = 0; i < nrcols; i++) {
    for (size_t j = 0; j < nrrows; j++)
      if (!fmpz_is_zero(fmpz_mat_entry(A,i,j)))
	goto next;
    for (size_t j = 0; j < nrcols; j++)
      result(nullity,j) = fmpz_get_si(fmpz_mat_entry(A,i,nrrows+j));
    nullity++;
  next:;
  }
  result.setsize(nullity,nrcols);
  
  return result;  
}

template<class T> sparse_mat<T> sparse_mat<T>::image(void) {
  fmpz_mat_t A;
  fmpz_mat_init(A, nrrows, nrcols);
  
  for (auto row: mat)
    for (auto col: row.second)
      fmpz_set_si(fmpz_mat_entry(A,row.first,col.first), col.second);

  fmpz_mat_hnf(A, A);

  sparse_mat<T> result;

  for (size_t i = 0; i < nrrows; i++)
    for (size_t j = 0; j < nrcols; j++) {
      T v = fmpz_get_si(fmpz_mat_entry(A,i,j));
      if (v)
	result(i,j) = v;
    }
  result.setsize();
  result.setsize(result.nrrows,nrcols);
  
  return result;  
}
  
#endif

template class sparse_mat<short>;
template class sparse_mat<long>;
template class sparse_mat<long long>;
