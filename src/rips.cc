/****************************************************************
 * compute presentations of Lie algebras with potentially
 * elements of delta_n \ gamma_n
 ****************************************************************/

#include <iostream>
#include <sstream>
#include <iterator>
#include <vector>
#include <map>
#include <time.h>

#include "rref.h"

typedef sparse_mat<long> mat_t;

/****************************************************************
 * fixed parameters:
 * a Lie algebra with generators x[0],x[1],...,x[d]
 * and relations C[i]*x[j] = sum A[i][j]*[x[j],x[d]]
 ****************************************************************/
#if 1 // original Rips example
const unsigned d = 3;
const int A[d][d] = {
  { 0, -4, -2 },
  { 4,  0, -1 },
  { 2,  1,  0 } };
const unsigned C[d] = { 64, 16, 4 };
#endif

#if 0
const unsigned d = 3;
int A[d][d] = {
  { 0, -4, -2 },
  { 4,  0, -1 },
  { 2,  1,  0 } };
const unsigned C[d] = { 729, 81, 9 };
#endif

#if 0
const unsigned d = 4;
int A[d][d] = {
  { 0, -128, -64, -16 },
  { 128, 0, -32, -8 },
  { 64, 32,  0, -1 },
  { 16, 8,  1,  0 } };
const unsigned C[d] = { 4096, 512, 64, 8 };
#endif

/****************************************************************
 * we do computations in Z / prime^exponent
 ****************************************************************/
const unsigned prime = 2, exponent = 10;

typedef std::vector<unsigned> ulist;

// convert a composition (i_1,...,i_r) with i_q >= 0 and sum i_j <= k
// to and from an integer
std::vector<ulist> pos2part;
std::map<ulist,unsigned> part2pos;

// convert a tuple (i_1,...,i_r) in {0,...,d-1}^r to and from an integer
std::vector<ulist> pos2tuple;
std::map<ulist,unsigned> tuple2pos;

void recursive_fill_part (unsigned lenremain, unsigned wtremain, ulist l)
{
  if (lenremain == 0) {
    unsigned pos = part2pos.size();
    pos2part.push_back(l);
    part2pos[l] = pos;
  } else
    for (unsigned i = 0; i < wtremain; i++) {
      l.push_back(i);
      recursive_fill_part (lenremain-1, wtremain-i, l);
      l.pop_back();
    }
}

void recursive_fill_tuple (unsigned lenremain, unsigned wtremain, ulist l)
{
  if (lenremain == 0) {
    unsigned pos = tuple2pos.size();
    pos2tuple.push_back(l);
    tuple2pos[l] = pos;
  } else
    for (unsigned i = 0; i < wtremain; i++) {
      l.push_back(i);
      recursive_fill_tuple (lenremain-1, wtremain, l);
      l.pop_back();
    }
}

void add_dynkin(mat_t::row_t &eq, unsigned t, int sign, size_t r, size_t s) {
  if (s == r)
    eq[t] += sign;
  else {    
    add_dynkin(eq, t, sign, r, s+1);
    ulist tuple = pos2tuple[t];
    unsigned j = tuple[s];
    for (size_t q = s; q > 0; q--)
      tuple[q] = tuple[q-1];
    tuple[0] = j;
    add_dynkin(eq, tuple2pos[tuple], -sign, r, s+1);
  }
}

void print_eq(mat_t::row_t e) {
  for (auto col: e)
    if (col.second != 0) {
      std::cout << col.second << "*(";
      std::copy(pos2tuple[col.first].begin(), pos2tuple[col.first].end(), std::ostream_iterator<unsigned>(std::cout, " "));
      std::cout << ") ";
    }
  std::cout << std::endl;
}

// find a basis of delta_{r+k} inside V^{otimes r}
mat_t rips(size_t r, size_t k, size_t numpart, size_t numtuple, size_t c) {
  mat_t eq;

  // compute left-normed commutators
  mat_t lie(numtuple, numtuple);
  for (size_t t = 0; t < numtuple; t++)
    add_dynkin(lie(t), t, -1, r, 1);
  
  // put equation that B_0 is a Lie element
  for (auto row: lie.nullspace().mat)
    for(auto col: row.second)
      eq(row.first,col.first) = col.second;
  eq.nrrows += numtuple;

  // put equations B_p = sum_s C *_s X_{p,s}
  for (size_t t = 0; t < numtuple; t++) {
    ulist tuple = pos2tuple[t];
    for (size_t p = 0; p < numpart; p++) {
      eq(eq.nrrows,t + numtuple*(0 + (r+1)*p)) = -1;
      for (size_t s = 0; s < r; s++)
	eq(eq.nrrows,t + numtuple*(s+1 + (r+1)*p)) = C[tuple[s]];
      eq.nrrows++;
    }
  }
  
  // put equation B_p = sum_s A *_s X_{p-e_s,s}
  // except for p=0, when equation is that B_0 is a Lie element
  for (size_t p = 1; p < numpart; p++) {
    ulist part = pos2part[p];
    unsigned prepart[r];
    for (size_t s = 0; s < r; s++) {
      if (part[s] == 0)
	prepart[s] = -1;
      else {
	part[s]--; prepart[s] = part2pos[part]; part[s]++;
      }
    }

    for (size_t t = 0; t < numtuple; t++) {
      ulist tuple = pos2tuple[t];
      eq(eq.nrrows,t + numtuple*(0 + (r+1)*p)) = -1;
      for (size_t s = 0; s < r; s++)
	if (prepart[s] != -1) {
	  unsigned j = tuple[s];
	  for (unsigned i = 0; i < d; i++) {
	    tuple[s] = i;
	    eq(eq.nrrows,tuple2pos[tuple] + numtuple*(s+1 + (r+1)*prepart[s])) = A[i][j];
	  }
	  tuple[s] = j;
	}
      eq.nrrows++;
    }
  }

  eq.setsize();

  mat_t sol0 = eq.nullspace();
  mat_t sol1; // kill all entries beyond the first, B_0
  for (auto row: sol0.mat)
    for (auto col: row.second)
      if (col.first < numtuple)
	sol1(row.first,col.first) = col.second;
  sol1.setsize(sol0.nrrows,numtuple);
  mat_t sol2 = sol1.image(), sol3;

  for (size_t row = 0; row < sol2.nrrows; row++) {
  restart: // super-inefficient!
    for (auto col: sol2(row))
      if (col.second != 0) {
	for (auto lierow: lie.mat)
	  for (auto liecol: lierow.second)
	    if (liecol.first == col.first && liecol.second != 0 && col.second % liecol.second == 0) { // can do reduction
	      sol3(row,lierow.first) += col.second / liecol.second;
	      add_dynkin(sol2(row), lierow.first, col.second / liecol.second, r, 1);
	      goto restart;
	    }
      }
  }
  sol3.setsize(sol2.nrrows,numtuple);
  return sol3;
}

void printpres(std::ostream &os, mat_t b, size_t c) {
  os << c << " < ";
  for (size_t i = 0; i < d; i++)
    os << "x" << i+1 << ", ";
  os << "z |\n";
  for (size_t i = 0; i < d; i++) {
    os << "\t" << C[i] << "*x" << i+1;
    for (size_t j = 0; j < d; j++)
      os << (j == 0 ? " = " : " + ") << A[i][j] << "*[x" << j+1 << ",z]";
    os << (i == d-1 ? " |" : ",") << std::endl;
  }
  for (size_t i = 0; i < b.nrrows; i++) {
    bool first = true;
    for (auto col: b(i)) {
      os << (first ? "\t" : " + ");
      first = true;
      os << col.second << "*[";
      for (auto j: pos2tuple[col.first])
	os << (first ? "" : ",") << "x" << j+1, first = false;
      os << "]";
    }
    os << (i == b.nrrows-1 ? " >" : ",") << std::endl;
  }
}

int main (int argc, char *argv[]) {
  if (argc != 4) {
    std::cerr << "Use: " << argv[0] << " <r> <k> <c>\n";
    return -1;
  }

  unsigned r = atoi(argv[1]);
  unsigned k = atoi(argv[2]);
  unsigned c = atoi(argv[3]);

  recursive_fill_part (r, k, ulist());
  recursive_fill_tuple (r, d, ulist());

  unsigned numpart = pos2part.size();
  unsigned numtuple = pos2tuple.size();

#if true
  {
#else
#if d == 4
  for (int i01 = 1; i01 <= 64; i01 *= 2)
    for (int i02 = 1; i02 <= i01; i02 *= 2)
      for (int i03 = 1; i03 <= i02; i03 *= 2)
	for (int i12 = 1; i12 <= i02; i12 *= 2)
	  for (int i13 = 1; i13 <= i12 && i13 <= i03; i13 *= 2)
	    for (int i23 = 1; i23 <= i13; i23 *= 2) {
#else
  for (int i01 = 1; i01 <= 243; i01 *= 3)
    for (int i02 = 1; i02 <= i01; i02 *= 3)
      for (int i12 = 1; i12 <= i02; i12 *= 3) {
#endif
	      A[0][1] = -i01; A[1][0] = i01;
	      A[0][2] = -i02; A[2][0] = i02;
	      A[1][2] = -i12; A[2][1] = i12;
#if d == 4
	      A[0][3] = -i03; A[3][0] = i03;
	      A[1][3] = -i13; A[3][1] = i13;
	      A[2][3] = -i23; A[3][2] = i23;
#endif
#endif
	      mat_t b = rips(r, k, numpart, numtuple, c);

	      std::stringstream pres;
  
	      printpres(pres, b, c);

	      std::cerr << pres.str();
	      
	      std::cout << pres.str();
	      std::cout.flush();
	
	      FILE *pipe = popen("./lienq - | awk '$3 == \"extra\" {on=1}; on{print;}'", "w");
	      fputs(pres.str().c_str(), pipe);
	      pclose(pipe);
	    }
  
  return 0;
}
