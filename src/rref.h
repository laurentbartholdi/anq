/****************************************************************
 * compute row echelon form of matrix over finite ring Z/p^e.
 * based on linbox.
 *
 * interface:
 * - create a sparse matrix m in class sparse_mat, with integer coefficients
 * - call m.rref(p, e).
 * The call returns a pair <reduced matrix, vector of pivot positions>.
 * each row has a "pivot" entry, which is a power of p. The coefficients
 * below the pivot are all 0, and those above are in [0,pivot).
 * each row is divisible by its pivot entry.
 ****************************************************************/

#include <iostream>
#include <iomanip>
#include <map>
#include <vector>

inline int getsparseformat() { 
  static int i = std::ios_base::xalloc();
  return i;
}

inline std::ostream& sparse_fmt(std::ostream& os) { os.iword(getsparseformat()) = true; return os; } 
inline std::ostream& dense_fmt(std::ostream& os) { os.iword(getsparseformat()) = false; return os; }


// generic sparse matrices, in row-major format
template<class T> class sparse_mat {
 public:
  typedef std::map<size_t, T> row_t;
  typedef std::map<size_t, row_t> mat_t;

  size_t nrrows, nrcols;
  mat_t mat;
  
  sparse_mat() { nrrows = nrcols = 0; }
  sparse_mat(size_t r, size_t c) { nrrows = r; nrcols = c; }
  
  std::ostream& sparse(std::ostream& os) { os.iword(getsparseformat()) = true; return os; } 
  std::ostream& dense(std::ostream& os) { os.iword(getsparseformat()) = false; return os; }


  inline T& operator()(size_t r, size_t c) { return mat[r][c]; }

  inline row_t& operator()(size_t r) { return mat[r]; }

  void setsize(void) {
    nrrows = nrcols = 0;
    for (auto row: mat) {
      if (row.second.size() > 0)
	nrrows = std::max(nrrows,row.first+1);
      for (auto col: row.second)
	nrcols = std::max(nrcols,col.first+1);
    }
  }

  void setsize(size_t r, size_t c) { nrrows = r; nrcols = c; }
  
  std::vector<T> operator*(const std::vector<T>& x) {  // compute y = mat*x
    std::vector<T> y(nrcols);

    for (auto row: mat) {
      T sum = 0;
      for (auto col: row.second)
	sum += col.second * x[col.first];
      y[row.first] = sum;
    }  
    return y;
  }

  friend std::ostream &operator<<(std::ostream &os, sparse_mat<T> const &m) {
    if (os.iword(getsparseformat())) {
      os << "sparse " << m.nrrows << " " << m.nrcols << std::endl;
      for (auto row: m.mat)
	for (auto col: row.second)
	  os << row.first << ' ' << col.first << ' ' << col.second << std::endl;
    } else {
      size_t nrcols = m.nrcols;
      for (auto row: m.mat) {
	os << std::right << std::setw(8) << row.first << ":[";
	size_t c = 0;
	for (auto col: row.second) {
	  while (c < col.first)
	    os << " 0", c++;
	  os << " " << col.second;
	  c = col.first + 1;
	}
	while (c < nrcols)
	  os << " 0", c++;
	os << " ]\n";
      }
    }
    return os;
  }
  
  std::pair<std::vector<T>,sparse_mat<T>> rref(size_t p, size_t e);

  sparse_mat<T> nullspace(); // return matrix whose rows generate the nullspace

  sparse_mat<T> image(); // return matrix whose rows generate the image
};
