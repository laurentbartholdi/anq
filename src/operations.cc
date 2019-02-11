/******************************************************************************
**
**                 Nilpotent Quotient for Lie Rings
** operations.c                                                 Csaba Schneider
**                                                           schcs@math.klte.hu
*/

#include "nq.h"
#include <map>

stack<hollowcvec> vecstack;

/* Lie algebra operations */
void hollowcvec::liebracket(const pcpresentation &pc, const hollowcvec v, const hollowcvec w) {
  coeff c;
  coeff_init(c);

  for (auto kcv : v)
    for (auto kcw : w)
      if (kcv.first <= pc.NrPcGens && kcw.first <= pc.NrPcGens && pc.Generator[kcv.first].w + pc.Generator[kcw.first].w <= pc.Class) {
	coeff_mul(c, kcv.second, kcw.second);
        if (kcv.first > kcw.first)
	  addmul(c, pc.Comm[kcv.first][kcw.first]);
	else if (kcw.first > kcv.first)
	  submul(c, pc.Comm[kcw.first][kcv.first]);
      }
  coeff_clear(c);
}

// add/subtract [[a,b],c]. sign == add, ~sign == subtract.
void hollowcvec::lie3bracket(const pcpresentation &pc, gen a, gen b, gen c, bool sign) {
  const bool sab = (a < b);
  const sparsecvec v = sab ? pc.Comm[b][a] : pc.Comm[a][b];
  
  for (auto kc : v) {
    if (kc.first > pc.NrPcGens)
      break;
    if (kc.first == c)
      continue;
    const bool skc = kc.first < c;
    const sparsecvec w = skc ? pc.Comm[c][kc.first] : pc.Comm[kc.first][c];
    if (sign ^ sab ^ skc)
      addmul(kc.second, w);
    else
      submul(kc.second, w);
  }
}

void hollowcvec::liecollect(const pcpresentation &pc) {
  coeff q;
  coeff_init(q);
  
  for (auto kc : *this)
    if(!coeff_reduced_p(kc.second, pc.Exponent[kc.first])) {
      coeff_fdiv_qr(q, (*this)[kc.first], kc.second, pc.Exponent[kc.first]);
      addmul(q, pc.Power[kc.first]);
    }
  coeff_clear(q);
}

/* group operations */
// the basic collector: this *= g^c
void hollowcvec::mul(const pcpresentation &pc, gen g, const coeff &c) {
  if (!coeff_cmp_si(c, 0))
    return;

  // check if coeff is reduced. if not, reduce !!!
  
  if (lower_bound(g) == end()) {
    coeff_set((*this)[g], c);
    return;
  }
  
  /*
!!!
general strategy: collect from the left.

keep a stack of elements to multiply. iterate backwards; while pos > g, remove from vector and put commutator (computed recursively with exponents) and monomials in stack. then drop c^g, and multiply recursively with everything on stack.
  */
}

// this *= v
void hollowcvec::mul(const pcpresentation &pc, const hollowcvec v) {
  for (auto kc : v)
    mul(pc, kc.first, kc.second);
}

// this *= v^-1*w. makes v=w in the process.
void hollowcvec::lquo(const pcpresentation &pc, hollowcvec v, const hollowcvec w) {
  /* we seek u with v u = w.
     say v = g^c * v', w = g^d * w'; then u = g^e * u' with e == d-c, and
     w = vu = v g^e u'; so we seek u' with (v g^e) u' = w, knowing that
     (v g^e) starts with g^d which we can skip.
  */
  
  auto pv = v.begin(), pw = w.begin();
  coeff c;
  coeff_init(c);

  for (;;) {
    gen g = INFINITY;
    bool minatv, minatw;
    if ((minatv = (pv != v.end()))) g = pv->first;
    if ((minatw = (pw != w.end()))) {
      if (pw->first > g) minatw = false;
      if (pw->first < g) g = pw->first, minatv = false;
    }
    else if (minatv && minatw)
      coeff_sub(c, (pw++)->second, pv->second);
    else if (minatv)
      coeff_neg(c, pv->second);
    else if (minatw)
      coeff_set(c, (pw++)->second);
    else
      break;
    if (!coeff_reduced_p(c, pc.Exponent[g]))
      coeff_fdiv_r(c, c, pc.Exponent[g]);
    mul(pc, g, c);
    v.mul(pc, g, c);
    pv = v.upper_bound(g);
  }
}

// this *= v^-1. modifies v in the process.
void hollowcvec::inv(const pcpresentation &pc, hollowcvec v) {
  /* we seek u with v u = 1.
     say v = g^c * v'; then u = g^d * u' with d == -c, and we have
     1 = vu = v g^d u'; so we seek u' with (v g^d) u' = 1, knowing that
     (v g^d) starts with a monomial >g.
  */
  coeff c;
  coeff_init(c);
  
  for (auto kc : v) {
    gen g = kc.first;
    coeff_neg (c, kc.second);
    if (!coeff_reduced_p(c, pc.Exponent[g]))
      coeff_fdiv_r(c, c, pc.Exponent[g]);
    mul(pc, g, c);
    v.mul(pc, g, c);
  }
  coeff_clear(c);
}

// multiply this with v^c. modifies v in the process.
static void pow(hollowcvec &r, const pcpresentation &pc, hollowcvec v, int c) {
  if (!c)
    return;

  if (c < 0) {
    hollowcvec i = vecstack.fresh();
    i.inv(pc, v);
    v.copy(i);
    vecstack.pop(i);
    c = -c;
  }

  for (;;) {
    if (c & 1)
      r.mul(pc, v);
    c >>= 1;
    if (!c)
      break;
    v.mul(pc, v);
  }
  
#if 0 // !!! premature optimization
  hollowcvec v2, v4;
  const unsigned base = (coeff_base <= 5) ? coeff_base : 2;
  // !!! also implement for 7? 
  if (base > 2)
    v2 = vecstack.fresh();
  if (base > 4)
    v4 = vecstack.fresh();
    
  if (c < 0) {
    hollowcvec i = vecstack.fresh();
    lquo(pc, i, v, i);
    v.copy(i);
    vecstack.pop(i);
    c = -c;
  }
  
  for (;;) {
    unsigned rem = c % base;
    bool did2 = false, did4 = false;
    switch (base) {
    case 2: if (rem) mul(v); break;
    case 3:
      if (rem & 2) {
	 rem -= 2;
	 v2.copy(v); v2.mul(v); did2 = true;
	 p.mul(v2);
      }
      if (rem) p.mul(v);
      break;
    case 5: if (rem & 2) {
	rem -= 2;
	v2.copy(v); v2.mul(v); did2 = true;
	p.mul(v2);
      }
      if (rem & 4) {
	rem -= 4;
	if (!did2) { v2.copy(v); v2.mul(v); did2 = true }
	v4.copy(v2); v4.mul(v2); did4 = true;
	p.mul(v4);
      }
      if (rem) p.mul(v);
    default:
      abortprintf(6, "Unimplemented power %u", base);
    }
    c /= base;
    if (!c)
      break;
    switch (base) {
    case 2: v.mul(v); break;
    case 3: if (!did2) { v2.copy(v); v2.mul(v); }
      v.mul(v2);
      break;
    case 5: if (!did2) { v2.copy(v); v2.mul(v); }
      if (!did4) { v4.copy(v2); v4.mul(v2); }
      v.mul(v4);
    }
  }
  if (base > 4)
    vecstack.pop(v4);
  if (base > 2)
    vecstack.pop(v2);
#endif
}

// this *= v^c
void hollowcvec::pow(const pcpresentation &pc, hollowcvec v, const coeff &c) {
  // !!! what should we do with coefficients that don't fit in a short?
  ::pow(*this, pc, v, coeff_get_si(c));
}

/* evaluate relator, given as tree */
void hollowcvec::eval(const pcpresentation &pc, node *rel) {
  switch (rel->type) {
  case TSUM:
    {
      eval(pc, rel->cont.bin.l);
      hollowcvec t = vecstack.fresh();
      t.eval(pc, rel->cont.bin.r);
      add(t);
      vecstack.pop(t);
    }
    break;
  case TPROD:
    if (rel->cont.bin.l->type == TNUM) {
      eval(pc, rel->cont.bin.r);
      mul(rel->cont.bin.l->cont.n);
    } else {
      eval(pc, rel->cont.bin.l);
      hollowcvec t = vecstack.fresh();
      t.eval(pc, rel->cont.bin.r);
      mul(pc, t);
      vecstack.pop(t);
    }
    break;
  case TQUO:
    {
      eval(pc, rel->cont.bin.l);
      hollowcvec t = vecstack.fresh();
      hollowcvec u = vecstack.fresh();
      t.eval(pc, rel->cont.bin.r);
      u.inv(pc, t);
      mul(pc, u);
      vecstack.pop(u);
      vecstack.pop(t);
    }
    break;
  case TLQUO:
#ifdef GROUP
  case TREL:
#endif
    {
      hollowcvec t = vecstack.fresh();
      hollowcvec u = vecstack.fresh();
      t.eval(pc, rel->cont.bin.l);
      u.eval(pc, rel->cont.bin.r);
      lquo(pc, t, u);
      vecstack.pop(u);
      vecstack.pop(t);
    }
    break;
  case TBRACK:
    {
      hollowcvec t = vecstack.fresh();
      hollowcvec u = vecstack.fresh();
      t.eval(pc, rel->cont.bin.l);
      u.eval(pc, rel->cont.bin.r);
#ifdef LIEALG
      liebracket(pc, t, u);
#else
      hollowcvec v = vecstack.fresh();
      v.copy(t);
      v.mul(pc, u); // v = t*u
      u.mul(pc, t); // u = u*t
      lquo(pc, u, v); // this = (u*t) \ (t*u)
      vecstack.pop(v);
#endif      
      vecstack.pop(u);
      vecstack.pop(t);
    }
    break;
  case TGEN:
    copysorted(pc.Epimorphism[rel->cont.g]);
    break;
  case TNEG:
    eval(pc, rel->cont.u);
    neg();
    break;
  case TINV:
    {
      hollowcvec t = vecstack.fresh();
      t.eval(pc, rel->cont.u);
      inv(pc, t);
      vecstack.pop(t);
    }
    break;
  case TDIFF:
#ifdef LIEALG
  case TREL:
#endif
    {
      eval(pc, rel->cont.bin.l);
      hollowcvec t = vecstack.fresh();
      t.eval(pc, rel->cont.bin.r);
      sub(t);
      vecstack.pop(t);
    }
    break;
  case TPOW:
    if (rel->cont.bin.r->type == TNUM) {
      hollowcvec t = vecstack.fresh();
      t.eval(pc, rel->cont.bin.l);
      pow(pc, t, rel->cont.bin.r->cont.n);
      vecstack.pop(t);
    } else {
      hollowcvec t = vecstack.fresh();
      hollowcvec u = vecstack.fresh();
      t.eval(pc, rel->cont.bin.l);
      u.eval(pc, rel->cont.bin.r);
      u.mul(pc, t);
      lquo(pc, t, u);
      vecstack.pop(u);
      vecstack.pop(t);
      break;
    }
    break;
  default:
    abortprintf(3, "EvalRel: operator of type %s should not occur", nodename[rel->type]);
  }
}

/* evaluate all relations, and add them to the relation matrix */
void EvalAllRel(const pcpresentation &pc, const fppresentation &pres) {
  for (auto n : pres.Aliases) {
    hollowcvec v = vecstack.fresh();
    v.eval(pc, n->cont.bin.r);
    v.liecollect(pc);

    if (Debug >= 2) {
      fprintf(LogFile, "# aliasing relation: ");
      PrintNode(LogFile, pres, n);
      fprintf(LogFile, " ("); PrintVec(LogFile, v); fprintf(LogFile, ")\n");
    }
    gen g = n->cont.bin.l->cont.g;
    pc.Epimorphism[g].resize(v.size());
    pc.Epimorphism[g].copy(v);
  }
  
  for (auto n : pres.Relators) {
    hollowcvec v = vecstack.fresh();
    v.eval(pc, n);
    v.liecollect(pc);

    if (Debug >= 2) {
      fprintf(LogFile, "# relation: ");
      PrintNode(LogFile, pres, n);
      fprintf(LogFile, " ("); PrintVec(LogFile, v); fprintf(LogFile, ")\n");
    }

    AddToRelMatrix(v);    
    vecstack.pop(v);
  }

  for (auto n : pres.Endomorphisms) {
    abortprintf(6,"Endomorphisms not yet implemented !!!");
  }

  TimeStamp("EvalAllRel()");
}
