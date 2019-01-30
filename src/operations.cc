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
void Sum(gpvec vec0, constgpvec vec1, constgpvec vec2) {
  gpvec p1 = vec1, p2 = vec2;
  for (;;) {
    if (p1->g == EOW) {
      Copy(vec0, p2);
      return;
    }
    if (p2->g == EOW) {
      Copy(vec0, p1);
      return;
    }
    if (p1->g < p2->g) {
      coeff_set(vec0->c, p1->c), vec0->g = p1->g;
      vec0++;
      p1++;
    } else if (p1->g > p2->g) {
      coeff_set(vec0->c, p2->c), vec0->g = p2->g;
      vec0++;
      p2++;
    } else {
      coeff_add(vec0->c, p1->c, p2->c);
      if (coeff_nz_p(vec0->c))
	vec0->g = p1->g, vec0++;
      p1++;
      p2++;
    }
  }
}

/* vec0 = vec1 + x2*vec2 */
void Sum(gpvec vec0, constgpvec vec1, const coeff x2, constgpvec vec2) {
  if (coeff_z_p(x2)) {
    Copy(vec0, vec1);
    return;
  }

  gpvec p1 = vec1, p2 = vec2;
  for (;;) {
    if (p1->g == EOW) {
      Prod(vec0, x2, p2);
      return;
    }
    if (p2->g == EOW) {
      Copy(vec0, p1);
      return;
    }
    if (p1->g < p2->g) {
      coeff_set(vec0->c, p1->c), vec0->g = p1->g;
      vec0++;
      p1++;
    } else if (p1->g > p2->g) {
      coeff_mul(vec0->c, x2, p2->c);
      if (coeff_nz_p(vec0->c))
	vec0->g = p2->g, vec0++;
      p2++;
    } else {
      coeff_set(vec0->c, p1->c);
      coeff_addmul(vec0->c, x2, p2->c);
      if (coeff_nz_p(vec0->c))
	vec0->g = p1->g, vec0++;
      p1++;
      p2++;
    }
  }
}

/* vec0 = x1*vec1 + x2*vec2 */
void Sum(gpvec vec0, const coeff x1, constgpvec vec1, const coeff x2, constgpvec vec2) {
  if (coeff_z_p(x1)) {
    Prod(vec0, x2, vec2);
    return;
  }
  if (coeff_z_p(x2)) {
    Prod(vec0, x1, vec1);
    return;
  }

  gpvec p1 = vec1, p2 = vec2;
  for (;;) {
    if (p1->g == EOW) {
      Prod(vec0, x2, p2);
      return;
    }
    if (p2->g == EOW) {
      Prod(vec0, x1, p1);
      return;
    }
    if (p1->g < p2->g) {
      coeff_mul(vec0->c, x1, p1->c);
      if (coeff_nz_p(vec0->c))
	vec0->g = p1->g, vec0++;
      p1++;
    } else if (p1->g > p2->g) {
      coeff_mul(vec0->c, x2, p2->c);
      if (coeff_nz_p(vec0->c))
	vec0->g = p2->g, vec0++;
      p2++;
    } else {
      coeff_mul(vec0->c, x1, p1->c);
      coeff_addmul(vec0->c, x2, p2->c);
      if (coeff_nz_p(vec0->c))
	vec0->g = p1->g, vec0++;
      p1++;
      p2++;
    }
  }
}

/* vec0 = vec1 - vec2 */
void Diff(gpvec vec0, constgpvec vec1, constgpvec vec2) {
  gpvec p1 = vec1, p2 = vec2;
  for (;;) {
    if (p1->g == EOW) {
      Neg(vec0, p2);
      return;
    }
    if (p2->g == EOW) {
      Copy(vec0, p1);
      return;
    }
    if (p1->g < p2->g) {
      coeff_set(vec0->c, p1->c), vec0->g = p1->g;
      vec0++;
      p1++;
    } else if (p1->g > p2->g) {
      coeff_neg(vec0->c, p2->c), vec0->g = p2->g;
      vec0++;
      p2++;
    } else {
      coeff_sub(vec0->c, p1->c, p2->c);
      if (coeff_nz_p(vec0->c))
	vec0->g = p1->g, vec0++;
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
void LieBracket(const pcpresentation &pc, gpvec vec0, constgpvec vec1, constgpvec vec2) {
  gpvec temp[2];
  bool parity = false;
  temp[0] = FreshVec();
  temp[1] = FreshVec();
  coeff c;
  coeff_init(c);
  
  for (auto gc1: vec1)
    for (auto gc2: vec2)
      if (gc1.g <= pc.NrPcGens && gc2.g <= pc.NrPcGens && pc.Generator[gc1.g].w + pc.Generator[gc2.g].w <= pc.Class) {
        if (gc1.g > gc2.g) {
	  coeff_mul(c, gc1.c, gc2.c);
	  Sum(temp[!parity], temp[parity], c, pc.Product[gc1.g][gc2.g]);
	  parity ^= 1;
	} else if (gc2.g > gc1.g) {
	  coeff_mul(c, gc1.c, gc2.c);
	  coeff_neg(c, c);
	  Sum(temp[!parity], temp[parity], c, pc.Product[gc2.g][gc1.g]);
	  parity ^= 1;
	}
      }
  coeff_clear(c);
  Copy(vec0, temp[parity]);
  PopVec();
  PopVec();
}

#ifdef LIEALG
/* the main collection routine. It could be optimized:
   if all Power relations have length n, and gv is full of length N,
   then the complexity is O(N^3) rather than O(N^2 n).

   We should do it with a container such as <map>
*/
void Collect(const pcpresentation &pc, gpvec vec0, constgpvec v) {
  gpvec temp[2], p;
  temp[0] = FreshVec();
  temp[1] = FreshVec();
  bool parity = false;
  coeff mp;
  coeff_init(mp);
  
  for (p = (gpvec) v; p->g != EOW;) {
    gen i = p->g;
    if(coeff_reduced_p(p->c, pc.Exponent[i])) {
      coeff_set(vec0->c, p->c), vec0->g = i;
      vec0++;
      p++;
    } else {
      coeff_fdiv_q(mp, p->c, pc.Exponent[i]);
      coeff_set(vec0->c, p->c);
      coeff_submul(vec0->c, mp, pc.Exponent[i]);
      if (coeff_nz_p(vec0->c))
	vec0->g = i, vec0++;
      p++;
      if (pc.Power[i] != nullgpvec && pc.Power[i]->g != EOW) {
	Sum(temp[!parity], p, mp, pc.Power[i]);
	parity ^= 1;
	p = temp[parity];
      }
    }
  }
  vec0->g = EOW;
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
void ShrinkCollect(const pcpresentation &pc, gpvec &v) {
  int shift = 0;
  gpvec p;
  for (p = v; p->g != EOW; p++) {
    gen g = p->g;
    if(!coeff_reduced_p(p->c, pc.Exponent[g])) {
      if (pc.Power[g] != nullgpvec && pc.Power[g]->g != EOW) { // bad news, collection can become longer
	gpvec newp = FreshVec();
	Collect(pc, newp, p);
	unsigned lenv = Length(v), lennewv = (p-v)+shift+Length(newp); //!!!
	if (lenv >= lennewv) {
	  Copy(p+shift, newp);
	  if (lenv > lennewv) {
	    int len = p-v; // !!!
	    v = ResizeVec(v, lenv, lennewv);
	    p = v + len;
	  }
	} else {
	  gpvec newv = NewVec(lennewv);
	  (p+shift)->g = EOW; // cut the vector for copy
	  Copy(newv, v);
	  (p+shift)->g = g; // put it back for deallocation
	  Copy(newv+(p-v)+shift, newp);
	  FreeVec(v);
	  v = newv;
	}
	PopVec();
	return;
      }
      coeff_fdiv_r(p->c, p->c, pc.Exponent[g]);
      if (coeff_z_p(p->c)) { shift--; continue; }
    }
    if (shift < 0)
      coeff_set((p+shift)->c, p->c), (p+shift)->g = g;
  }
  if (shift < 0) {
    (p+shift)->g = EOW;
    v = ResizeVec(v, v-p, (v-p)+shift);
  }
}
#else
void Collect(const pcpresentation &pc, gpvec vec0, constgpvec v) {
  volatile int x = 0; printf("%d", x / x);
  //!!! GROUP
}

// time-critical: avoid copying if possible
void ShrinkCollect(const pcpresentation &pc, gpvec &v) {
  volatile int x = 0; printf("%d", x / x);
  //!!! GROUP
}
#endif

void Prod(const pcpresentation &pc, gpvec vec0, constgpvec vec1, constgpvec vec2)
{
  Copy(vec0, vec1);
  Collect(pc, vec0, vec2);
}

// solve vec2*vec0 = vec1*vec2 for vec0
void Conjugate(const pcpresentation &pc, gpvec vec0, constgpvec vec1, constgpvec vec2)
{
  gpvec p1p2 = FreshVec();
  Copy(p1p2, vec1);
  Collect(pc, p1p2, vec2);
  LQuo(pc, vec0, vec2, p1p2);
  PopVec();
}

void Quo(const pcpresentation &pc, gpvec vec0, constgpvec vec1, constgpvec vec2)
{
  gpvec vec2i = FreshVec();
#if 0
  //!!! check order in which we push inverse!
  for (autounsigned pos = 0; vec2[pos].g != EOW; pos++) {
    vec2i[pos].g = vec2[pos].g;
    coeff_neg(vec2i[pos].c, vec2[pos].c);
  }
#endif
  Copy(vec0, vec1);
  Collect(pc, vec0, vec2i);
  PopVec();
}

// solve vec1*vec0 = vec2 for vec0
void LQuo(const pcpresentation &pc, gpvec vec0, constgpvec vec1, constgpvec vec2)
{
  gpvec p = vec0, p1 = vec1, p2 = FreshVec();
  Copy(p2, vec2);
  p->g = EOW;
  
  while (gen g = std::min(vec1->g, vec2->g) != EOW) {
    if (p1->g == p2->g)
      coeff_sub(p->c, (p2++)->c, (p1++)->c);
    else if (g == p1->g)
      coeff_neg(p->c, (p1++)->c);
    else
      coeff_set(p->c, (p2++)->c);
    if (!coeff_reduced_p(p->c, pc.Exponent[g]))
      coeff_fdiv_r(p->c, p->c, pc.Exponent[g]);
    if (coeff_nz_p(p->c)) {
      (p++)->g = g;
      p->g = EOW;
      Collect(pc, p2, p-1);
    }
  }
  PopVec();
}

gcoeff __one = { .g = EOW };
const gpvec one = { .data = &__one };

void Inv(const pcpresentation &pc, gpvec vec0, constgpvec vec1)
{
  LQuo(pc, vec0, vec1, one);
}

// solve vec2*vec1*vec0 = vec1*vec2 for vec0
void GroupBracket(const pcpresentation &pc, gpvec vec0, constgpvec vec1, constgpvec vec2)
{
  // at each step, we have p2a*p1a*p = p1p2
  gpvec p1a = FreshVec(), p2a = FreshVec(), p1p2 = FreshVec(), p = vec0;
  Copy(p1p2, vec1);
  Collect(pc, p1p2, vec2);
  Copy(p1a, vec1);
  Copy(p2a, vec2);
  p->g = EOW;
  
  while (gen g = std::min(p1p2->g,std::min(p1a->g,p2a->g)) != EOW) {
    if (g == p1a->g)
      coeff_neg(p->c, p1a->c); // increment later p1a, after more collecting
    else
      coeff_set_si(p->c, 0);
    if (g == p2a->g)
      coeff_sub(p->c, p->c, (p2a++)->c);
    if (g == p1p2->g)
      coeff_add(p->c, p->c, (p1p2++)->c);
    if (!coeff_reduced_p(p->c, pc.Exponent[g]))
      coeff_fdiv_r(p->c, p->c, pc.Exponent[g]);
    if (coeff_nz_p(p->c)) {
      (p++)->g = g;
      p->g = EOW;
      Collect(pc, p1a, p-1);
    }
    if (g == p1a->g) {
      gen oldg = (++p1a)->g;
      p1a->g = EOW;
      Collect(pc, p2a, p1a-1);
      p1a->g = oldg;
    }
  }
  PopVec(), PopVec(), PopVec(), PopVec();
}

static void Pow(const pcpresentation &pc, gpvec vec0, constgpvec vec1, int c)
{
  if (c == -1) {
    Inv(pc, vec0, vec1);
    return;
  }
  if(c == 0) {
    vec0->g = EOW;
    return;
  }
  if (c == 1) {
    Copy(vec0, vec1);
    return;
  }

  vec0->g = EOW;
  gpvec s = FreshVec();
  if (c > 0)
    Copy(s, vec1);
  else {
    Inv(pc, s, vec1);
    c = -c;
  }

  //!!! use prime instead of 2 to improve cancellations
  for (;;) {
    if (c % 2)
      Collect(pc, vec0, s);
    c /= 2;
    if (c == 0)
      break;
    Collect(pc, s, s);
  }
  PopVec();
}

void Pow(const pcpresentation &pc, gpvec vec0, constgpvec vec1, coeff &c)
{
  //!!! what to do with large exponents?
  Pow(pc, vec0, vec1, coeff_get_si(c));
}

#if 0
// work-in-progress attempt
typedef std::map<gen,coeff> sparsevec;

void Collect(gpvec &vec, bool resize) {
  sparsevec todo;
  int pos, shift;
  coeff mp;
  coeff_init(mp);
  for (pos = shift = 0; vec[pos].g != EOW; pos++) {
    gen g = vec[pos].g;
    if(!coeff_reduced_p(vec[pos].c, Exponent[g])) {
      coeff_fdiv_q(mp, vec[pos].c, Exponent[g]);
      coeff_submul(vec[pos].c, mp, Exponent[g]);
      if (coeff_nz_p(vec[pos].c) && (Power[g] == NULL || Power[g]->g == EOW))
	goto next;  // just reduce the coeff, trivial power
      if (Power[g] == NULL || Power[g]->g == EOW) {
	shift++; // we're about to shrink the vector, a coefficient vanished
	continue;
      }
      // insert Power[g] into todo. When looping, compare elements and head of todo; pop whichever comes first, maybe add, reduce, maybe push more on todo.

      // simpler, probably equivalent in performance: push Power and all of remainder of word on todo (combining). Then repeatedly remove head of todo, reduce, maybe push back a Power, and write into vec. If reached EOW, either realloc or keep writing.
    }
  next:
    if (shift)
      coeff_set(vec[pos-shift].c, vec[pos].c), vec[pos-shift].g = g;
  }
  coeff_clear(mp);
}

void Collect(gpvec v0, constgpvec v1) {
  Collect((gpvec) v1, false);
  Copy(v0, v1);
}

void ShrinkCollect(gpvec &v) {
  Collect(v, true);
}
#endif
