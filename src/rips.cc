/****************************************************************
 * compute presentations of Lie algebras with potentially
 * elements of delta_n \ gamma_n
 ****************************************************************/

#include <iostream>
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
const unsigned d = 3;
const int A[d][d] = {
  { 0, -4, -2 },
  { 4,  0, -1 },
  { 2,  1,  0 } };
const unsigned C[d] = { 64, 16, 4 };

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
  for (size_t i = 0; i < e.size(); i++)
    if (e[i] != 0) {
      std::cout << e[i] << "*(";
      std::copy(pos2tuple[i].begin(), pos2tuple[i].end(), std::ostream_iterator<unsigned>(std::cout, " "));
      std::cout << ") ";
    }
  std::cout << std::endl;
}

// find a basis of delta_{r+k} inside V^{otimes r}
mat_t rips(size_t r, size_t k, size_t numpart, size_t numtuple, size_t c) {
  mat_t eq;

  // put equation that B_0 is a Lie element
  {
    mat_t lie(numtuple, numtuple);
    for (size_t t = 0; t < numtuple; t++)
      add_dynkin(lie(t), t, -1, r, 1);
    lie = lie.nullspace();
    for (auto row: lie.mat)
      for(auto col: row.second)
	eq(row.first,col.first) = col.second;
    eq.nrrows += numtuple;
  }

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

  //  std::cout << eq << std::endl;
  
  mat_t sol0 = eq.nullspace();
  mat_t sol1; // kill all entries beyond the first, B_0
  for (auto row: sol0.mat)
    for (auto col: row.second)
      if (col.first < numtuple)
	sol1(row.first,col.first) = col.second;
  sol1.setsize(sol0.nrrows,numtuple);
  return sol1.image();
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

  mat_t b = rips(r, k, numpart, numtuple, c);

  std::cout << b << std::endl;

  for (size_t i = 0; i < b.nrrows; i++)
    print_eq(b(i));
  
  return 0;

  std::cout << "pos2tuple:" << std::endl;
  for (unsigned i = 0; i < pos2tuple.size(); i++) {
    std::cout << i << " -> ";
    std::copy(pos2tuple[i].begin(), pos2tuple[i].end(), std::ostream_iterator<unsigned>(std::cout, " "));
    std::cout << std::endl;
  }

  std::cout << "tuple2pos:" << std::endl;
  for (auto p: tuple2pos) {
    std::copy(p.first.begin(), p.first.end(), std::ostream_iterator<unsigned>(std::cout, " "));
    std::cout << " -> " << p.second << std::endl;
  }
}
#if 0
liesolve := function(file,A,C,maxk)
    local mats, n, i, j;
    n := Length(A);
    mats := ripssolve(A,C,maxk);
    PrintTo(file,"< ",JoinStringsWithSeparator(List([1..n],i->Concatenation("x",String(i))),","),",x0 |\n");
    for i in [1..n] do
        AppendTo(file,"\t",C[i,i],"*x",i," = ",JoinStringsWithSeparator(List([1..n],j->Concatenation(String(A[i,j]),"*[x",String(j),",x0]"))," + "));
        if i=n then AppendTo(file," |\n"); else AppendTo(file,",\n"); fi;
    od;
    for i in [1..Length(mats)] do
        AppendTo(file,"\t",JoinStringsWithSeparator(List(Combinations([1..n],2),p->Concatenation(String(mats[i][p[1],p[2]]),"*[x",String(p[1]),",x",String(p[2]),"]"))," + "));
        if i=Length(mats) then AppendTo(file, ">\n"); else AppendTo(file,",\n"); fi;
    od;
end;
#endif
