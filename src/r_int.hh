/****************************************************************
 * a simple arithmetic interface.
 * integer<K> represents integers on 64*K bits;
 * integer<0> is unbounded precision (gmp), and integer<1>=int64_t
 * implements init(), clear(),
 * add, sub, mul, fdiv, ... similarly to gmp interface.
 ****************************************************************/

template<unsigned K=1> class integer {
};

#include "r_int0.hh"
#include "r_int1.hh"
