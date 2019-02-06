/******************************************************************************
**
**                 Nilpotent Quotient for Lie Rings
** operations.c                                                 Csaba Schneider
**                                                           schcs@math.klte.hu
*/

#include "nq.h"
#include <map>

/*
** The purpose of this couple of functions is to handle the Lie-algebra
** operations in the PC-presentation. There are 3 main operations i.e.
** a summation:        with respect to this the elements form an Abelian-group;
** a Lie product:      equipped with the usual Jacoby, anti-commutativity, and
**                     distributivity. It is stored in the Power[][] matrix.
** an integer-product: A module-operation of course. Makes no problem(?).
*/

/****************************************************************
 vector addition and scalar multiplication
****************************************************************/
/* vec0 = vec1 + vec2 */
void Sum(sparsecvec vec0, const sparsecvec vec1, const sparsecvec vec2) {
  auto p0 = vec0.begin(), p1 = vec1.begin(), p2 = vec2.begin();
  for (;;) {
    if (p1.atend()) {
      p0.tail().copy(p2.tail());
      return;
    }
    if (p2.atend()) {
      p0.tail().copy(p1.tail());
      return;
    }
    if (p1->first < p2->first) {
      coeff_set(p0->second, p1->second), p0->first = p1->first;
      p0++;
      p1++;
    } else if (p1->first > p2->first) {
      coeff_set(p0->second, p2->second), p0->first = p2->first;
      p0++;
      p2++;
    } else {
      coeff_add(p0->second, p1->second, p2->second);
      if (coeff_nz_p(p0->second))
	p0->first = p1->first, p0++;
      p1++;
      p2++;
    }
  }
}

/* vec0 = vec1 + x2*vec2 */
void Sum(sparsecvec vec0, const sparsecvec vec1, const coeff x2, const sparsecvec vec2) {
  if (coeff_z_p(x2)) {
    vec0.copy(vec1);
    return;
  }

  auto p0 = vec0.begin(), p1 = vec1.begin(), p2 = vec2.begin();
  for (;;) {
    if (p1.atend()) {
      Prod(p0.tail(), x2, p2.tail());
      return;
    }
    if (p2.atend()) {
      p0.tail().copy(p1.tail());
      return;
    }
    if (p1->first < p2->first) {
      coeff_set(p0->second, p1->second), p0->first = p1->first;
      p0++;
      p1++;
    } else if (p1->first > p2->first) {
      coeff_mul(p0->second, x2, p2->second);
      if (coeff_nz_p(p0->second))
	p0->first = p2->first, p0++;
      p2++;
    } else {
      coeff_set(p0->second, p1->second);
      coeff_addmul(p0->second, x2, p2->second);
      if (coeff_nz_p(p0->second))
	p0->first = p1->first, p0++;
      p1++;
      p2++;
    }
  }
}

/* vec0 = x1*vec1 + x2*vec2 */
void Sum(sparsecvec vec0, const coeff x1, const sparsecvec vec1, const coeff x2, const sparsecvec vec2) {
  if (coeff_z_p(x1)) {
    Prod(vec0, x2, vec2);
    return;
  }
  if (coeff_z_p(x2)) {
    Prod(vec0, x1, vec1);
    return;
  }

  auto p0 = vec0.begin(), p1 = vec1.begin(), p2 = vec2.begin();
  for (;;) {
    if (p1.atend()) {
      Prod(p0.tail(), x2, p2.tail());
      return;
    }
    if (p2.atend()) {
      Prod(p0.tail(), x1, p1.tail());
      return;
    }
    if (p1->first < p2->first) {
      coeff_mul(p0->second, x1, p1->second);
      if (coeff_nz_p(p0->second))
	p0->first = p1->first, p0++;
      p1++;
    } else if (p1->first > p2->first) {
      coeff_mul(p0->second, x2, p2->second);
      if (coeff_nz_p(p0->second))
	p0->first = p2->first, p0++;
      p2++;
    } else {
      coeff_mul(p0->second, x1, p1->second);
      coeff_addmul(p0->second, x2, p2->second);
      if (coeff_nz_p(p0->second))
	p0->first = p1->first, p0++;
      p1++;
      p2++;
    }
  }
}

/* vec0 = vec1 - vec2 */
void Diff(sparsecvec vec0, const sparsecvec vec1, const sparsecvec vec2) {
  auto p0 = vec0.begin(), p1 = vec1.begin(), p2 = vec2.begin();
  for (;;) {
    if (p1.atend()) {
      Neg(p0.tail(), p2.tail());
      return;
    }
    if (p2.atend()) {
      p0.tail().copy(p1.tail());
      return;
    }
    if (p1->first < p2->first) {
      coeff_set(p0->second, p1->second), p0->first = p1->first;
      p0++;
      p1++;
    } else if (p1->first > p2->first) {
      coeff_neg(p0->second, p2->second), p0->first = p2->first;
      p0++;
      p2++;
    } else {
      coeff_sub(p0->second, p1->second, p2->second);
      if (coeff_nz_p(p0->second))
	p0->first = p1->first, p0++;
      p1++;
      p2++;
    }
  }
}

/****************************************************************
 Lie bracket of vectors

 !!! this could be very inefficient the way it's implemented:
 if vec1 and vec2 are almost full vectors (of length N), and each
 Product[] entry is a short vector (of length n), then we have
 complexity O(N^3) while we could achieve O(N^2n) in theory.

 it would be better to do this with a container storing all
 coefficients of all sums of Product[]s, and reading the results from
 there into vec0.
****************************************************************/
/* vec0 = [ vec1, vec2 ] */
void LieBracket(const pcpresentation &pc, sparsecvec vec0, const sparsecvec vec1, const sparsecvec vec2) {
  sparsecvec temp[2];
  bool parity = false;
  temp[0] = FreshVec();
  temp[1] = FreshVec();
  coeff c;
  coeff_init(c);
  
  for (auto gc1 : vec1)
    for (auto gc2 : vec2)
      if (gc1.first <= pc.NrPcGens && gc2.first <= pc.NrPcGens && pc.Generator[gc1.first].w + pc.Generator[gc2.first].w <= pc.Class) {
        if (gc1.first > gc2.first) {
	  coeff_mul(c, gc1.second, gc2.second);
	  Sum(temp[!parity], temp[parity], c, pc.Product[gc1.first][gc2.first]);
	  parity ^= 1;
	} else if (gc2.first > gc1.first) {
	  coeff_mul(c, gc1.second, gc2.second);
	  coeff_neg(c, c);
	  Sum(temp[!parity], temp[parity], c, pc.Product[gc2.first][gc1.first]);
	  parity ^= 1;
	}
      }
  coeff_clear(c);
  vec0.copy(temp[parity]);
  PopVec();
  PopVec();
}

#ifdef LIEALG
/* the main collection routine. It could be optimized:
   if all Power relations have length n, and gv is full of length N,
   then the complexity is O(N^3) rather than O(N^2 n).

   We should do it with a container such as <map>
*/
// !!!
void Collect(const pcpresentation &pc, sparsecvec vec0, const sparsecvec v) {
  sparsecvec temp[2];
  temp[0] = FreshVec();
  temp[1] = FreshVec();
  bool parity = false;
  coeff mp;
  coeff_init(mp);
  auto p = v.begin(), p0 = vec0.begin();
  
  for (; !p.atend();) {
    gen i = p->first;
    if(coeff_reduced_p(p->second, pc.Exponent[i])) {
      coeff_set(p0->second, p->second), p0->first = i;
      p0++;
      p++;
    } else {
      coeff_fdiv_q(mp, p->second, pc.Exponent[i]);
      coeff_set(p0->second, p->second);
      coeff_submul(p0->second, mp, pc.Exponent[i]);
      if (coeff_nz_p(p0->second))
	p0->first = i, p0++;
      p++;
      if (!pc.Power[i].empty()) {
	Sum(temp[!parity], p.tail(), mp, pc.Power[i]);
	parity ^= 1;
	p = temp[parity].begin();
      }
    }
  }
  p0.markend();
  PopVec();
  PopVec();
  coeff_clear(mp);
}

/* It seems the following routine is time-critical.
   It can be improved in many manners:
  -- if Power[g]->g != EOW but we're at the end (likely case), can just append
  -- if shift<0, or reduced coeff=0, we may have space to accomodate Power[g]
  -- we should use a std::map in the full collect, see above
*/
void ShrinkCollect(const pcpresentation &pc, sparsecvec &v) {
  int shift = 0;
  unsigned pos;
  for (pos = 0; !v.issize(pos); pos++) {
    gen g = v[pos].first;
    if(!coeff_reduced_p(v[pos].second, pc.Exponent[g])) {
      if (!pc.Power[g].empty()) { // bad news, collection can become longer
	sparsecvec newp = FreshVec();
	Collect(pc, newp, v.window(pos));
	unsigned lenv = v.size(), lennewv = pos+shift+newp.size();
	if (lenv >= lennewv) {
	  v.window(pos+shift).copy(newp);
	  if (lenv > lennewv)
	    v.resize(lenv, lennewv);
	} else {
	  sparsecvec newv(lennewv);
	  v.truncate(pos+shift); // cut the vector for copy
	  newv.copy(v);
	  v[pos+shift].first = g; // put it back for deallocation
	  newv.window(pos+shift).copy(newp);
	  v.free();
	  v = newv;
	}
	PopVec();
	return;
      }
      coeff_fdiv_r(v[pos].second, v[pos].second, pc.Exponent[g]);
      if (coeff_z_p(v[pos].second)) { shift--; continue; }
    }
    if (shift < 0)
      coeff_set(v[pos+shift].second, v[pos].second), v[pos+shift].first = g;
  }
  if (shift < 0) {
    v.truncate(pos+shift);
    v.resize(pos,pos+shift);
  }
}
#else
/* in groups, collection is done during calculation of the operations.
 * the last collection step consists just in removing 0s.
 */
void Collect(const pcpresentation &pc, sparsecvec vec0, const sparsecvec v) {
  volatile int x = 0; printf("%d", x / x);
  //!!! GROUP
}

// time-critical: avoid copying if possible
void ShrinkCollect(const pcpresentation &pc, sparsecvec &v) {
  volatile int x = 0; printf("%d", x / x);
  //!!! GROUP
}
#endif

/* the main collection function, for groups */
void GroupCollect(const pcpresentation &pc, sparsecvec vec0, const sparsecvec v) {
}

void Prod(const pcpresentation &pc, sparsecvec vec0, const sparsecvec vec1, const sparsecvec vec2)
{
  vec0.copy(vec1);
  GroupCollect(pc, vec0, vec2);
}

// solve vec2*vec0 = vec1*vec2 for vec0
void Conjugate(const pcpresentation &pc, sparsecvec vec0, const sparsecvec vec1, const sparsecvec vec2)
{
  sparsecvec p1p2 = FreshVec();
  p1p2.copy(vec1);
  GroupCollect(pc, p1p2, vec2);
  LQuo(pc, vec0, vec2, p1p2);
  PopVec();
}

void Quo(const pcpresentation &pc, sparsecvec vec0, const sparsecvec vec1, const sparsecvec vec2)
{
  sparsecvec vec2i = FreshVec();
#if 0
  //!!! check order in which we push inverse!
  for (autounsigned pos = 0; vec2[pos].g != EOW; pos++) {
    vec2i[pos].g = vec2[pos].g;
    coeff_neg(vec2i[pos].second, vec2[pos].second);
  }
#endif
  vec0.copy(vec1);
  GroupCollect(pc, vec0, vec2i);
  PopVec();
}

// solve vec1*vec0 = vec2 for vec0
void LQuo(const pcpresentation &pc, sparsecvec vec0, const sparsecvec vec1, const sparsecvec vec2)
{
#if 0
  sparsecvec p = vec0, p1 = vec1, p2 = FreshVec();
  p2.Copy(p2, vec2);
  p->first = EOW;
  
  while (gen g = std::min(vec1->first, vec2->first) != EOW) {
    if (p1->first == p2->first)
      coeff_sub(p->second, (p2++)->second, (p1++)->second);
    else if (g == p1->first)
      coeff_neg(p->second, (p1++)->second);
    else
      coeff_set(p->second, (p2++)->second);
    if (!coeff_reduced_p(p->second, pc.Exponent[g]))
      coeff_fdiv_r(p->second, p->second, pc.Exponent[g]);
    if (coeff_nz_p(p->second)) {
      p->first = g;
      (p+1)->first = EOW;
      GroupCollect(pc, p2, p);
      p++;
    }
  }
  PopVec();
#endif
}

const sparsecvec one((size_t) 0);

void Inv(const pcpresentation &pc, sparsecvec vec0, const sparsecvec vec1)
{
  LQuo(pc, vec0, vec1, one);
}

// solve vec2*vec1*vec0 = vec1*vec2 for vec0
void GroupBracket(const pcpresentation &pc, sparsecvec vec0, const sparsecvec vec1, const sparsecvec vec2)
{
#if 0 // !!!
  // at each step, we have p2a*p1a*p = p1p2
  sparsecvec p1a = FreshVec(), p2a = FreshVec(), p1p2 = FreshVec(), p = vec0;
  Copy(p1p2, vec1);
  GroupCollect(pc, p1p2, vec2);
  Copy(p1a, vec1);
  Copy(p2a, vec2);
  p->first = EOW;
  
  while (gen g = std::min(p1p2->first,std::min(p1a->first,p2a->first)) != EOW) {
    if (g == p1a->first)
      coeff_neg(p->second, p1a->second); // increment later p1a, after more collecting
    else
      coeff_set_si(p->second, 0);
    if (g == p2a->first)
      coeff_sub(p->second, p->second, (p2a++)->second);
    if (g == p1p2->first)
      coeff_add(p->second, p->second, (p1p2++)->second);
    if (!coeff_reduced_p(p->second, pc.Exponent[g]))
      coeff_fdiv_r(p->second, p->second, pc.Exponent[g]);
    if (coeff_nz_p(p->second)) {
      p->first = g;
      (p+1)->first = EOW;
      GroupCollect(pc, p1a, p);
      p++;
    }
    if (g == p1a->first) {
      gen oldg = (++p1a)->first;
      p1a->first = EOW;
      GroupCollect(pc, p2a, p1a+(-1));
      p1a->first = oldg;
    }
  }
  PopVec(), PopVec(), PopVec(), PopVec();
#endif
}

static void Pow(const pcpresentation &pc, sparsecvec vec0, const sparsecvec vec1, int c)
{
  if (c == -1) {
    Inv(pc, vec0, vec1);
    return;
  }
  if(c == 0) {
    vec0.clear();
    return;
  }
  if (c == 1) {
    vec0.copy(vec1);
    return;
  }

  vec0.clear();
  sparsecvec s = FreshVec();
  if (c > 0)
    s.copy(vec1);
  else {
    Inv(pc, s, vec1);
    c = -c;
  }

  //!!! use prime instead of 2 to improve cancellations
  for (;;) {
    if (c % 2)
      GroupCollect(pc, vec0, s);
    c /= 2;
    if (c == 0)
      break;
    GroupCollect(pc, s, s);
  }
  PopVec();
}

void Pow(const pcpresentation &pc, sparsecvec vec0, const sparsecvec vec1, coeff &c)
{
  //!!! what to do with large exponents?
  Pow(pc, vec0, vec1, coeff_get_si(c));
}

#if 0
// work-in-progress attempt
typedef std::map<gen,coeff> sparsevec;

void Collect(sparsecvec vec, bool resize) {
  sparsevec todo;
  int pos, shift;
  coeff mp;
  coeff_init(mp);
  for (pos = shift = 0; vec[pos].g != EOW; pos++) {
    gen g = vec[pos].g;
    if(!coeff_reduced_p(vec[pos].second, Exponent[g])) {
      coeff_fdiv_q(mp, vec[pos].second, Exponent[g]);
      coeff_submul(vec[pos].second, mp, Exponent[g]);
      if (coeff_nz_p(vec[pos].second) && Power[g].empty())
	goto next;  // just reduce the coeff, trivial power
      if (Power[g].empty()) {
	shift++; // we're about to shrink the vector, a coefficient vanished
	continue;
      }
      // insert Power[g] into todo. When looping, compare elements and head of todo; pop whichever comes first, maybe add, reduce, maybe push more on todo.

      // simpler, probably equivalent in performance: push Power and all of remainder of word on todo (combining). Then repeatedly remove head of todo, reduce, maybe push back a Power, and write into vec. If reached EOW, either realloc or keep writing.
    }
  next:
    if (shift)
      coeff_set(vec[pos-shift].second, vec[pos].second), vec[pos-shift].g = g;
  }
  coeff_clear(mp);
}

void Collect(sparsecvec v0, const sparsecvec v1) {
  Collect((sparsecvec) v1, false);
  Copy(v0, v1);
}

void ShrinkCollect(sparsecvec &v) {
  Collect(v, true);
}
#endif
