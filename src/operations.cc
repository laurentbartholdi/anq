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
void hollowcvec::mul(const pcpresentation &pc, const hollowcvec) {
}

void hollowcvec::pow(const pcpresentation &pc, const hollowcvec, const coeff &) {
}

void hollowcvec::quo(const pcpresentation &pc, const hollowcvec) {
}

void hollowcvec::lquo(const pcpresentation &pc, const hollowcvec, const hollowcvec) {
}

void hollowcvec::conjugate(const pcpresentation &pc, const hollowcvec, const hollowcvec) {
}

void hollowcvec::groupbracket(const pcpresentation &pc, const hollowcvec, const hollowcvec) {
}

void hollowcvec::groupcollect(const pcpresentation &pc) {
}

#if 0
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
#endif

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
      t.eval(pc, rel->cont.bin.r);
      quo(pc, t);
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
      liebracket(pc, t, u);
      vecstack.pop(u);
      vecstack.pop(t);
    }
    break;
  case TBRACE:
    {
      hollowcvec t = vecstack.fresh();
      hollowcvec u = vecstack.fresh();      
      t.eval(pc, rel->cont.bin.l);
      u.eval(pc, rel->cont.bin.r);
      groupbracket(pc, t, u);
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
      quo(pc, t);
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
      conjugate(pc, t, u);
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
  
  TimeStamp("EvalAllRel()");
}

/* check consistency of pc presentation, and deduce relations to
 * impose on centre
 */

// !!!GROUP

/*
**  The relations to be enforced are of form
**  [ a, b, c ] + [ b, c, a ] + [ c, a, b ]    where <a> is of weight 1
**  and  <a> < <b> < <c>  with respect to the linear ordering of the
**  generators.
*/
static void CheckJacobi(const pcpresentation &pc, gen a, gen b, gen c) {
  hollowcvec t = vecstack.fresh();
  t.lie3bracket(pc, a, b, c, true);
  t.lie3bracket(pc, b, c, a, true);
  t.lie3bracket(pc, c, a, b, true);
  t.liecollect(pc);

  if (Debug >= 2) {
    fprintf(LogFile, "# consistency: jacobi(a%d,a%d,a%d) = ", a, b, c);
    PrintVec(LogFile, t);
    fprintf(LogFile, "\n");
  }

  AddToRelMatrix(t);

  vecstack.pop(t);
}

/*
**  The following function checks the consistency relation for
**  o_i[ a, b ] = [ (( o_ia )), b ] where (()) means the substitution
**  of the argument with its relation.
**
*/
static void CheckPower(const pcpresentation &pc, gen a, gen b) {
  hollowcvec t = vecstack.fresh();
  
  for (auto kc : pc.Power[a]) {
    gen g = kc.first;
    if (g > pc.NrPcGens)
      break;
    if (g > b)
      t.submul(kc.second, pc.Comm[g][b]);
    else if (g < b)
      t.addmul(kc.second, pc.Comm[b][g]);
  }

  if (a > b)
    t.addmul(pc.Exponent[a], pc.Comm[a][b]);
  else if (a < b)
    t.submul(pc.Exponent[a], pc.Comm[b][a]);
  t.liecollect(pc);

  if (Debug >= 2) {
    fprintf(LogFile, "# consistency: ");
    coeff_out_str(LogFile, pc.Exponent[a]);
    fprintf(LogFile, "*[a%d,a%d]-[", a, b);
    coeff_out_str(LogFile, pc.Exponent[a]);
    fprintf(LogFile, "*a%d,a%d] = ", a, b);
    PrintVec(LogFile, t);
    fprintf(LogFile, "\n");
  }

  AddToRelMatrix(t);
  
  vecstack.pop(t);
}

/* if N*v = 0 in our ring, and we have a power relation A*g = w,
 * enforce (N/A)*w = 0
 */
static void CheckTorsion(const pcpresentation &pc, unsigned i) {
  hollowcvec t = vecstack.fresh();
  coeff annihilator, unit;
  coeff_init(annihilator);
  coeff_init(unit); // unused
  
  coeff_unit_annihilator(unit, annihilator, pc.Exponent[i]);
  t.addmul(annihilator, pc.Power[i]);
  t.liecollect(pc);
  
  if (Debug >= 2) {
    fprintf(LogFile, "# consistency: ");
    coeff_out_str(LogFile, annihilator);
    fprintf(LogFile, "*");
    coeff_out_str(LogFile, pc.Exponent[i]);
    fprintf(LogFile, "*a%d = ", i);
    PrintVec(LogFile, t);
    fprintf(LogFile, "\n");
  }

  AddToRelMatrix(t);

  coeff_clear(unit);
  coeff_clear(annihilator);
  vecstack.pop(t);
}

void Consistency(const pcpresentation &pc) {
  for (unsigned i = 1; i <= pc.NrPcGens; i++) {
    if (pc.Generator[i].t != DGEN)
      continue;
    for (unsigned j = i + 1; j <= pc.NrPcGens; j++)
      for (unsigned k = j + 1; k <= pc.NrPcGens; k++) {
	unsigned totalweight = pc.Generator[i].w + pc.Generator[j].w + pc.Generator[k].w;
	if (totalweight > pc.Class || (pc.Graded && totalweight != pc.Class))
	  continue;
	
        CheckJacobi(pc, i, j, k);
      }
  }
  
  for (unsigned i = 1; i <= pc.NrPcGens; i++)
    if (coeff_nz_p(pc.Exponent[i])) {
      CheckTorsion(pc, i);

      for (unsigned j = 1; j <= pc.NrPcGens; j++) {
	unsigned totalweight = pc.Generator[i].w + pc.Generator[j].w;
	if (totalweight > pc.Class || (pc.Graded && totalweight != pc.Class))
	  continue;
  	
	CheckPower(pc, i, j);
      }
    }
  
  TimeStamp("Consistency()");
}
