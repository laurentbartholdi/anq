/******************************************************************************
**
**                 Nilpotent Quotient for Lie Rings
** presentation.c                                               Csaba Schneider
**                                                           schcs@math.klte.hu
*/

#include "nq.h"
#include <vector>
#include <deque>

#ifdef ASSOCALG
static sparsepcvec unit_vector(gen g)
{
  sparsepcvec v;
  v.alloc(1);
  v.truncate(1);
  v[0].first = g;
  v[0].second.set_si(1);
  return v;
}
#endif

/* initialize Pc presentation, at class 0. No products or powers are set yet. */
pcpresentation::pcpresentation(const fppresentation &pres) : fp(pres) {
  NrPcGens = 0;
  Class = 0;
  LastGen = {0};
  
  Epimorphism.resize(pres.NrGens + 1);
  Epimorphism[0] = sparsepcvec::bad(); // guard
  for (unsigned i = 1; i <= pres.NrGens; i++)
    Epimorphism[i].alloc(0);
  
  Generator.resize(1);
#ifdef ASSOCALG
  Generator[0] = {.type = DUNIT, .w = 0, .cw = 0};  
#else
  Generator[0] = {.type = DINVALID};
#endif

  /* we initialize the exponents and annihilators of our pc generators */
  Exponent.reserve(1);
  //Annihilator.resize(NrPcGens + 1);

  Power.resize(1);
  Power[0] = sparsepcvec::bad(); // guard

#ifdef ASSOCALG
  Prod.resize(NrPcGens + 1);
  Prod[0].resize(NrPcGens + 1);
  Prod[0][0] = unit_vector(0);
#else
  Comm.resize(NrPcGens + 1);
#endif

  TimeStamp("pcpresentation::pcpresentation()");  
}

pcpresentation::~pcpresentation() {
#ifdef ASSOCALG // starts at 0; we only free Prod[0][i] and Prod[i][0] once
  for (unsigned i = 0; i <= NrPcGens; i++)
    for (unsigned j = (i > 0); j <= NrPcGens; j++)
      Prod[i][j].free();
#endif
  for (unsigned i = 1; i <= NrPcGens; i++) {
    if (Power[i].allocated())
      Power[i].free();
    Exponent[i].clear();
    Annihilator[i].clear();
#ifndef ASSOCALG
    for (unsigned j = 1; j < i; j++)
      Comm[i][j].free();
#endif
  }
  for (unsigned i = 1; i <= fp.NrGens; i++)
    Epimorphism[i].free();
}

#ifdef GROUP
// return fresh tail to (f*g)*h / f*(g*h), with f > g > h
static hollowpcvec tail_assoc(const pcpresentation &pc, gen f, gen g, gen h) {
  hollowpcvec rhs = vecstack.fresh();
  hollowpcvec lhs = vecstack.fresh();
  
  set_si(lhs[f], 1);
  lhs.mul(pc, h);
  lhs.mul(pc, g);
  lhs.mul(pc, pc.Comm[g][h]); // lhs = f*(g*h) = f*h*g*[g,h]
  
  set_si(rhs[f], 1);
  rhs.mul(pc, g);
  rhs.mul(pc, h); // rhs = (f*g)*h

  rhs.sub(lhs);
  vecstack.release(lhs);

  return rhs;
}

// return fresh tail of power relation. Here g is torsion, pc.Exponent[g]=N>0.
// if f>g: it's f*g^N \ f*g*g^(N-1)
// if f=g: it's f^N*f \ f*f^N
// if f<g: it's g^N*f \ g^(N-1)*f*g*[g,f]
static hollowpcvec tail_pow(const pcpresentation &pc, gen f, gen g) {
  hollowpcvec rhs = vecstack.fresh();
  hollowpcvec lhs = vecstack.fresh();
  
  if (f > g) { /* f*g*g^(N-1) = f*g^N */
    set_si(lhs[f], 1);
    lhs.mul(pc, g);
    add_si(rhs[g], pc.Exponent[g], -1);
    lhs.mul(pc, rhs);
    rhs.clear();
    
    set_si(rhs[f], 1);
    rhs.mul(pc, pc.Power[g]);
  } else if (f < g) { /* g^N*f = g^(N-1)*f*g*[g,f] */
    lhs.copy(pc.Power[g]);
    lhs.mul(pc, f);

    add_si(rhs[g], pc.Exponent[g], -1);
    rhs.mul(pc, f);
    rhs.mul(pc, g);
    rhs.mul(pc, pc.Comm[g][f]);
  } else { /* f*f^N = f^N*f */
    lhs.copy(pc.Power[f]);
    lhs.mul(pc, f);

    set_si(rhs[f], 1);
    rhs.mul(pc, pc.Power[f]);
  }
  rhs.sub(lhs);
  vecstack.release(lhs);

  return rhs;
}
#endif

// should [i,j] receive a tail?
inline bool pcpresentation::isgoodweight_comm(int i, int j) const {
  unsigned totalweight = Generator[i].w + Generator[j].w;

  if (totalweight > Class)
    return false;

  if (Graded && totalweight != Class)
    return false;

  unsigned totalcweight = Generator[i].cw + Generator[j].cw;

  if (totalcweight > NilpotencyClass)
    return false;
  
  if (Metabelian && Generator[i].cw > 1 && Generator[j].cw > 1)
    return false;

  return true;  
}

/* add generator newgen to vector v, and store its definition */
void pcpresentation::add1generator(sparsepcvec &v, deftype def) {
  unsigned len = v.size();
  v.resize(len+1);
  v[len].first = ++NrTotalGens;
  set_si(v[len].second, 1);
  v.truncate(len+1);

  Generator.resize(NrTotalGens + 1);
  Generator[NrTotalGens] = def;
}

/* The first step, to extend a pc presentation one class ahead, is to
 * define new generators for all relations which are not definitions,
 * the so-called "tails".
 */
unsigned pcpresentation::addtails() {
  NrTotalGens = NrPcGens;

  /* inverse lookup tables:
     - is_dgen[i] == (exist g: Generator[g] = {DGEN,i}), so fp generator i is used to define a pc generator, or is an alias
     is_dpow[i] == (exist g: Generator[g] = {DPOW,i}), so ai^Exponent[i] = ag
     is_dcomm[i][j] == (exist g: Generator[g] = {DCOMM,i,j}), so [ai,aj] = ag
     is_dprod[i][j] == (exist g: Generator[g] = {DCOMM,i,j}), so ai*aj = ag
  */
  std::vector<bool> is_dgen(fp.NrGens+1,false);
  std::vector<bool> is_dpow(NrPcGens+1,false);
#ifdef ASSOCALG
  std::vector<std::vector<bool>> is_dprod(NrPcGens+1);
#else
  std::vector<std::vector<bool>> is_dcomm(NrPcGens+1);
#endif
  
  /* first mark aliases */
  for (const auto &n : fp.Aliases)
    is_dgen[n->l->g] = true;
    
  for (unsigned i = 1; i <= NrPcGens; i++) {
#ifdef ASSOCALG
    is_dprod[i] = std::vector<bool>(NrPcGens+1,false);
#else
    is_dcomm[i] = std::vector<bool>(i,false);
#endif
    
    switch (Generator[i].type) {
#ifdef ASSOCALG
    case DCOMM:
      is_dprod[Generator[i].g][Generator[i].h] = true;
      break;
#else
    case DCOMM:
      is_dcomm[Generator[i].g][Generator[i].h] = true;
      break;
#endif
    case DGEN:
      is_dgen[Generator[i].s] = true;
      break;
    case DPOW:
      is_dpow[Generator[i].p] = true;
      break;
    default:
      abortprintf(4, "Generator %d should have been eliminated", i);
    }
  }

  for (unsigned weight = (Graded ? Class : 1); weight <= Class; weight++) {
    /* add tails to powers.  for all pc generators g with
       Exponent[g]!=0, add a tail to Power[g], unless:
       - g is defined as a power
       
       - we're in graded, torsion mode (so producing a
       (Z/torsion)[t]-algebra) and g has degree < Class-1
    */
    for (unsigned i = 1; i <= NrPcGens; i++) {
      if (is_dpow[i])
	continue;
      if (!Jacobson && z_p(Exponent[i]))
	  continue;
#ifdef GROUP
      unsigned totalweight = Jennings ? Generator[i].w*pccoeff::characteristic : Generator[i].w+1;
#elif defined(LIEALG)
      unsigned totalweight = Jacobson ? Generator[i].w*pccoeff::characteristic : Generator[i].w+1;
#elif defined(ASSOCALG)
      unsigned totalweight = Generator[i].w+1;
#endif
      if (totalweight != weight)
	continue;
      
      const deftype newdeftype = {.type = (weight == Class ? DPOW : TEMPPOW), .w = Class, .cw = Generator[i].cw, {.p = i}};
      add1generator(Power[i], newdeftype);
      if (Debug >= 2)
#ifdef GROUP
	fprintf(LogFile, "# added tail a%d to weight-%d non-defining torsion a%d^" PRIpccoeff "\n", NrTotalGens, Generator[i].w, i, &Exponent[i]);
#else
        fprintf(LogFile, "# added tail a%d to weight-%d non-defining torsion " PRIpccoeff "*a%d\n", NrTotalGens, Generator[i].w, &Exponent[i], i);
#endif
    }
    
    /* for all non-power pc generators g of weight <=Class-k and all
       defining pc generators h of weight k, with g > h, and such
       that [g,h] is not defining, add a tail to Comm[g][h].

       all other tails will be computed in Tails() out of these:
       - if h is not defining, using Jacobi or Z-linearity;
       - if g is a power, using Z-linearity.

       we have to first add weights of low class, and then higher, to
	 be sure that the generator that will be kept after
	 consistency and relations are imposed is a valid defining
	 generator (namely, of totalweight = Class). */
    for (unsigned i = 1; i <= NrPcGens; i++) {
      if (Generator[i].type != DGEN)
	continue;
#ifdef ASSOCALG
      for (unsigned j = 1; j <= NrPcGens; j++) {
	if (is_dprod[j][i])
	  continue;
	unsigned totalweight = Generator[i].w+Generator[j].w;
	if (totalweight != weight)
	  continue;

	if (!isgoodweight_comm(i, j))
	  continue;

	add1generator(Prod[j][i], {.type = (weight == Class ? DCOMM : TEMPCOMM), .w = Class, .cw = Generator[i].cw+Generator[j].cw, {{.g = j, .h = i}}});
	if (Debug >= 2)
	  fprintf(LogFile, "# added tail a%d to weight-%d non-defining product a%d*a%d\n", NrTotalGens, totalweight, j, i);
      }
#else
      for (unsigned j = i+1; j <= NrPcGens; j++) {
	if (is_dcomm[j][i])
	  continue;
#ifdef LIEALG // it's too complicated to compute the tail in groups, let's just set it.
	if (Generator[j].type == DPOW)
	  continue;
#endif
	unsigned totalweight = Generator[i].w+Generator[j].w;
	if (totalweight != weight)
	  continue;

	if (!isgoodweight_comm(i, j))
	  continue;

	add1generator(Comm[j][i], {.type = (weight == Class ? DCOMM : TEMPCOMM), .w = Class, .cw = Generator[i].cw+Generator[j].cw, {{.g = j, .h = i}}});
	if (Debug >= 2)
	  fprintf(LogFile, "# added tail a%d to weight-%d non-defining commutator [a%d,a%d]\n", NrTotalGens, totalweight, j, i);
      }
#endif
    }
    
    /* add tails to the non-defining fp generators. */
    for (unsigned i = 1; i <= fp.NrGens; i++) {
      if (is_dgen[i] || fp.Weight[i] != weight)
	continue;

      // weird bug with gnu g++ 8.1.0: cannot accept newgentype as argument
      const deftype newdeftype = deftype{.type = (weight == Class ? DGEN : TEMPGEN), .w = Class, .cw = 1, {.s = i}};
      add1generator(Epimorphism[i], newdeftype);
      if (Debug >= 2)
	fprintf(LogFile, "# added tail a%d to epimorphic image of degree-%u generator %s\n", NrTotalGens, fp.Weight[i], fp.GeneratorName[i].c_str());
    }
  }

  /* Extend the arrays of exponents, commutators etc. to the necessary
   *  size.  Let's define the newly introduced generators to be
   *  central i.e.  All of their product relations will be trivial and
   *  also they have coefficients 0.
   */
  Exponent.resize(NrTotalGens + 1);
  for (unsigned i = NrPcGens + 1; i <= NrTotalGens; i++) {
    Exponent[i].init();
    Exponent[i].kernel<matcoeff>();
  }

  Annihilator.resize(NrTotalGens + 1);
  for (unsigned i = NrPcGens + 1; i <= NrTotalGens; i++)
    Annihilator[i].init_set_si(0);

  Power.resize(NrTotalGens + 1);
  for (unsigned i = NrPcGens + 1; i <= NrTotalGens; i++)
    Power[i].noalloc();

  /* Unless we're in the associative algebra case, the Comm array
     is not extended yet, because anyways it won't be used. */
#ifdef ASSOCALG
  Prod.resize(NrTotalGens + 1);
  Prod[0].resize(NrTotalGens + 1);
  for (unsigned i = NrPcGens + 1; i <= NrTotalGens; i++) {
    Prod[i].resize(1);
    Prod[i][0] = Prod[0][i] = unit_vector(i);
  }
#endif

  // set the size of vectors in the vector stack, since we'll soon
  // have to do some collecting
  vecstack.setsize(NrTotalGens);

  if (Debug >= 2)
    fprintf(LogFile, "# added new tails, total number of generators is %u\n", NrTotalGens);

  /* Some of the newly introduced generators strictly depend on one
   * another hence we can compute them inductively.
   */
  for (unsigned j = NrPcGens; j >= 1; j--) {
#ifdef ASSOCALG
    for (unsigned i = 1; i <= NrPcGens; i++) {
      if (!isgoodweight_comm(i, j))
	continue;
	  
      if (Generator[i].type == DGEN) /* nothing to do, aj*ai is a defining generator */
	  continue;

      hollowpcvec tail = vecstack.fresh();

    /* compute the correct tail for aj*ai: in associative algebra
     * - if ai is defined as g*h, compute aj*ai = (aj*g)*h
     * - if ai is defined as N*g, compute aj*ai = N*(aj*g)
     */

      if (Generator[i].type == DCOMM) { /* ai = g*h */
	gen g = Generator[i].g, h = Generator[i].h;
	tail.assocprod(*this, Prod[j][g], h);
	tail.collect(*this);

	if (Debug >= 2)
	  fprintf(LogFile, "# tail: a%d*a%d = (a%d*a%d)*a%d = " PRIhollowpcvec "\n", j, i, j, g, h, &tail);
      } else if (Generator[i].type == DPOW) { /* ai = N*g */
	gen g = 0;
	if (Debug >= 2)
	  fprintf(LogFile, "# tail: [a%d,a%d] = " PRIpccoeff "*[a%d,a%d] = " PRIhollowpcvec "\n", j, i, &Exponent[g], j, g, &tail);
      } else if (Generator[j].type == DPOW) { /* aj = N*g */
	gen g = 0;
	if (Debug >= 2)
	  fprintf(LogFile, "# tail: [a%d,a%d] = " PRIpccoeff "*[a%d,a%d] = " PRIhollowpcvec "\n", j, i, &Exponent[g], g, i, &tail);
      } else
	abortprintf(4, "AddTails: unknown definition for [a%d,a%d]", j, i);
      
      unsigned len = 0;
      auto tp = tail.begin();
      for (const auto &kc : Prod[j][i]) {
	if (kc.first != (*tp).first || cmp(kc.second,(*tp).second))
	  abortprintf(5, "AddTails: adjustment to tail of [a%d,a%d] doesn't lie in centre", j, i);
	len++;
	tp++;
      }

      if (tp != tail.end()) {
	Prod[j][i].resize(len, tail.size());
	Prod[j][i].window(len).copy(tp, tail.end());
      }
      vecstack.release(tail);
    }
#elif defined(LIEALG)
    for (unsigned i = 1; i < j; i++) {
      if (!isgoodweight_comm(i, j))
	continue;
	  
      if (Generator[i].type == DGEN && Generator[j].type != DPOW) /* nothing to do, [aj,ai] is a defining generator */
	continue;

      hollowpcvec tail = vecstack.fresh();

      /* compute the correct tail for [aj,ai]: in Lie algebra,
       * - if ai is defined as [g,h], compute [aj,ai] = [aj,g,h]-[aj,h,g]
       * - if ai is defined as N*g, compute [aj,ai] = N*[aj,g]
       * - if aj is defined as N*g, compute [aj,ai] = N*[g,ai] or -N*[ai,g].
       */

      if (Generator[i].type == DCOMM) { /* ai = [g,h] */
	gen g = Generator[i].g, h = Generator[i].h;
	tail.lie3bracket(*this, j, g, h, true); // +[[aj,g],h]
	tail.lie3bracket(*this, j, h, g, false); // -[[aj,h],g]
	tail.collect(*this);

	if (Debug >= 2)
	  fprintf(LogFile, "# tail: [a%d,a%d] = [a%d,[a%d,a%d]] = " PRIhollowpcvec "\n", j, i, j, g, h, &tail);
      } else if (Generator[i].type == DPOW) { /* ai = N*g */
	gen g = Generator[i].p;
	if (Jacobson)
	  tail.engel(*this, j, g, pccoeff::characteristic, true);
	else
	  tail.addmul(Exponent[g], Comm[j][g]);
	tail.collect(*this);

	if (Debug >= 2)
	  fprintf(LogFile, "# tail: [a%d,a%d] = " PRIpccoeff "*[a%d,a%d] = " PRIhollowpcvec "\n", j, i, &Exponent[g], j, g, &tail);
      } else if (Generator[j].type == DPOW) { /* aj = N*g */
	gen g = Generator[j].p;
	if (Jacobson)
	  tail.engel(*this, i, g, pccoeff::characteristic, false);
	else {
	  if (g > i)
	    tail.addmul(Exponent[g], Comm[g][i]);
	  else if (g < i)
	    tail.submul(Exponent[g], Comm[i][g]);
	}
	tail.collect(*this);

	if (Debug >= 2)
	  fprintf(LogFile, "# tail: [a%d,a%d] = " PRIpccoeff "*[a%d,a%d] = " PRIhollowpcvec "\n", j, i, &Exponent[g], g, i, &tail);
      } else
	abortprintf(4, "AddTails: unknown definition for [a%d,a%d]", j, i);
      
      unsigned len = 0;
      auto tp = tail.begin();
      for (const auto &kc : Comm[j][i]) {
	if (kc.first != (*tp).first || cmp(kc.second,(*tp).second))
	  abortprintf(5, "AddTails: adjustment to tail of [a%d,a%d] doesn't lie in centre", j, i);
	len++;
	tp++;
      }

      if (tp != tail.end()) {
	Comm[j][i].resize(len, tail.size());
	Comm[j][i].window(len).copy(tp, tail.end());
      }
      vecstack.release(tail);
    }
#elif defined(GROUP)
    for (unsigned i = 1; i < j; i++) {
      if (!isgoodweight_comm(i, j))
	continue;
	  
      if (Generator[i].type == DGEN) /* nothing to do, [aj,ai] is a defining generator */
	  continue;

      hollowpcvec tail;

      /* compute the correct tail for [aj,ai]: in groups,
       * - if ai is defined as [g,h], compute [aj,ai] *= (aj(gh))^-1 * (ajg)h
       * - if ai is defined as g^N, compute [aj,ai] *= (aj g^N)^-1 * (ajg)g^(N-1)
       * - if aj is defined as g^N, compute [aj,ai] *= (g^N a_i)^-1 * (g^(N-1)*(g*a_i))
       */

      if (Generator[i].type == DCOMM) { /* ai = [g,h] */
	tail = tail_assoc(*this, j, Generator[i].g, Generator[i].h);

	if (Debug >= 2)
	  fprintf(LogFile, "# tail: [a%d,a%d] = [a%d,[a%d,a%d]] *= " PRIhollowpcvec "\n", j, i, j, Generator[i].g, Generator[i].h, &tail);
      } else if (Generator[i].type == DPOW) { /* ai = g^N */
	tail = tail_pow(*this, j, Generator[i].p);
	tail.neg();

	if (Debug >= 2)
	  fprintf(LogFile, "# tail: [a%d,a%d] = [a%d,a%d^" PRIpccoeff "] *= " PRIhollowpcvec "\n", j, i, j, Generator[i].p, &Exponent[Generator[i].p], &tail);
      } else if (Generator[j].type == DPOW) { /* aj = g^N */
	abortprintf(4, "AddTails: Generators[%d].type == DPOW shouldn't occur", j);
	// @@@ unused now; tail seems too hard to compute because of
	// order in which the commutators are set up
	tail = tail_pow(*this, i, Generator[j].p);

	if (Debug >= 2)
	  fprintf(LogFile, "# tail: [a%d,a%d] = [a%d^" PRIpccoeff ",a%d] *= " PRIhollowpcvec "\n", j, i, Generator[j].p, &Exponent[Generator[j].p], i, &tail);
      } else
	abortprintf(4, "AddTails: unknown definition for [a%d,a%d]", j, i);

      if (!tail.empty()) {
	if (tail.begin()->first <= NrPcGens)
	  abortprintf(5, "Addtails: adjustment to tail of [a%d,a%d] doesn't lie in centre", j, i);

	unsigned len = Comm[j][i].size();
	
	Comm[j][i].resize(len, len+tail.size());
	Comm[j][i].window(len).copy(tail);
      }
      vecstack.release(tail);
    }
#endif
  }
  
  TimeStamp("pcpresentation::addtails()");

  return NrTotalGens - NrPcGens;
}

/* check consistency of pc presentation, and deduce relations to
 * impose on centre
 */
void pcpresentation::consistency(matrix &m) const {
  // check Jacobi identity
  for (unsigned i = 1; i <= NrPcGens; i++) {
    if (Generator[i].type != DGEN)
      continue;

    unsigned commi = (Generator[i].cw > 1);

    for (unsigned j = (1-INT_ASSOCALG)*i + 1; j <= NrPcGens; j++) {
      unsigned commij = commi + (Generator[j].cw > 1);
      if (Metabelian && commij >= 2)
	continue;
      
      for (unsigned k = (1-INT_ASSOCALG)*j + 1; k <= NrPcGens; k++) {
	unsigned totalweight = Generator[i].w + Generator[j].w + Generator[k].w;
	if (totalweight > Class || (Graded && totalweight != Class))
	  continue;
	
	if (Metabelian && commij + (Generator[k].cw > 1) >= 2)
	  continue;
	
#ifdef LIEALG
	hollowpcvec t = vecstack.fresh();
	t.lie3bracket(*this, i, j, k, true);
	t.lie3bracket(*this, j, k, i, true);
	t.lie3bracket(*this, k, i, j, true);
	t.collect(*this);

	if (Debug >= 2)
	  fprintf(LogFile, "# consistency: jacobi(a%d,a%d,a%d) = " PRIhollowpcvec "\n", i, j, k, &t);
#elif defined(GROUP)
	hollowpcvec t = tail_assoc(*this, k, j, i);

	if (Debug >= 2)
	  fprintf(LogFile, "# consistency: associator(a%d,a%d,a%d) = " PRIhollowpcvec "\n", k, j, i, &t);
#elif defined(ASSOCALG)
	hollowpcvec t = vecstack.fresh();
	t.assocprod(*this, Prod[j][i], k, true);
	t.assocprod(*this, j, Prod[i][k], false);
	t.collect(*this);
	if (Debug >= 2)
	  fprintf(LogFile, "# consistency: associator(a%d,a%d,a%d) = " PRIhollowpcvec "\n", j, i, k, &t);
#endif
	m.queuerow(t);	
	vecstack.release(t);
      }
    }
  }
  
  pccoeff annihilator;
  annihilator.init();

  // check torsion relations
  for (unsigned i = 1; i <= NrPcGens; i++)
    if (Jacobson || nz_p(Exponent[i])) {
      /* if N*v = 0 in our ring, and we have a power relation A*g = w,
       * enforce (N/A)*w = 0.
       * if the group's exponent is given (by the torsion in the
       * ccoefficients), impose a power relation.
       */

      if (!Jacobson) {
	hollowpcvec t = vecstack.fresh();
	
	unit_annihilator(nullptr, &annihilator, Exponent[i]);
#ifdef GROUP
	hollowpcvec u = vecstack.fresh();
	u.copy(Power[i]);      
	t.pow(*this, u, annihilator);
	vecstack.release(u);
      
	if (Debug >= 2)
	  fprintf(LogFile, "# consistency: (a%d^" PRIpccoeff ")^" PRIpccoeff " = " PRIhollowpcvec "\n", i, &Exponent[i], &annihilator, &t);
#else
	t.addmul(annihilator, Power[i]);
	t.collect(*this);
  
	if (Debug >= 2)
	  fprintf(LogFile, "# consistency: " PRIpccoeff "*" PRIpccoeff "*a%d = " PRIhollowpcvec "\n", &annihilator, &Exponent[i], i, &t);
#endif      
	m.queuerow(t);
	vecstack.release(t);
      }
      
      for (unsigned j = 1; j <= NrPcGens; j++) {
	if (!isgoodweight_comm(i, j))
	  continue;
#ifdef LIEALG
	/* two different meanings:
	 * - in usual Lie algebras, enforce
	     N*[a,b] = [N*a,b] if N is the order of a;
	 * - in restricted Lie algebras, enforce [a,b,...,b] = [a,b^p] */
	hollowpcvec t = vecstack.fresh();

	// first, we compute -[N*ai,aj] or -[ai^p,aj]
	for (const auto &kc : Power[i]) {
	  gen g = kc.first;
	  if (g > NrPcGens)
	    break;
	  if (g > j)
	    t.submul(kc.second, Comm[g][j]);
	  else if (g < j)
	    t.addmul(kc.second, Comm[j][g]);
	}

	if (Jacobson)
	  t.engel(*this, j, i, pccoeff::characteristic, false);
	else {
	  if (i > j)
	    t.addmul(Exponent[i], Comm[i][j]);
	  else if (i < j)
	   t.submul(Exponent[i], Comm[j][i]);
	}
	t.collect(*this);
	
	if (Debug >= 2) {
	  if (Jacobson)
	    fprintf(LogFile, "# consistency: [a%d,a%d,...,a%d]-[a%d,a%d^p] = " PRIhollowpcvec "\n", j, i, i, j, i, &t);
	  else
	    fprintf(LogFile, "# consistency: " PRIpccoeff "*[a%d,a%d]-[" PRIpccoeff "*a%d,a%d] = " PRIhollowpcvec "\n", &Exponent[i], i, j, &Exponent[i], i, j, &t);	   
	}
#elif defined(GROUP)
	/* enforce a^N*b = a^(N-1)*(a*b) or a*b^N = (a*b)*b^(N-1) in groups
	 */
	hollowpcvec t = tail_pow(*this, j, i);
	
	if (Debug >= 2)
	 fprintf(LogFile, "# consistency: associator(a%d,a%d,a%d^(N-1)) = " PRIhollowpcvec "\n", j, i, i, &t);
#elif defined(ASSOCALG)
	/* enforce N*(a*b) = (N*a)*b and N*(b*a) = b*(N*a) if N is the order of a */
	hollowpcvec t = vecstack.fresh();

	t.assocprod(*this, Power[i], j, false);
	t.addmul(Exponent[i], Prod[i][j]);
	t.collect(*this);
	if (Debug >= 2)
	  fprintf(LogFile, "# consistency: " PRIpccoeff "*(a%d*a%d)-(" PRIpccoeff "*a%d)*a%d = " PRIhollowpcvec "\n", &Exponent[i], i, j, &Exponent[i], i, j, &t);
	m.queuerow(t);

	t.clear();
	t.assocprod(*this, j, Power[i], false);
	t.addmul(Exponent[i], Prod[j][i]);
	t.collect(*this);
	if (Debug >= 2)
	  fprintf(LogFile, "# consistency: " PRIpccoeff "*(a%d*a%d)-a%d*(" PRIpccoeff "*a%d) = " PRIhollowpcvec "\n", &Exponent[i], j, i, j, &Exponent[i], i, &t);
#endif	
	m.queuerow(t);
	vecstack.release(t);
      }
    }
  
  annihilator.clear();

  TimeStamp("pcpresentation::consistency()");
}

// compute result = src^phi, except for the symbol g in src
void MapEndo(hollowpcvec &result, const pcpresentation &pc, sparsepcvec src, gen avoid, const sparsepcmat &phi) {
  for (const auto &kc : src) {
    if (kc.first == avoid)
      continue;
#ifdef GROUP
    hollowpcvec p = vecstack.fresh();
    p.copy(phi[kc.first]);
    result.pow(pc, p, kc.second);
    vecstack.release(p);
#else
    result.addmul(kc.second, phi[kc.first]);
#endif
  }
}

// Evaluate all relations in pc, ship them to Matrix
void pcpresentation::evalrels(matrix &m) {
  for (const auto &n : fp.Aliases) {
    hollowpcvec v = vecstack.fresh();
    v.eval(*this, n->r);
    v.collect(*this);

    if (Debug >= 2) {
      fprintf(LogFile, "# aliasing relation: ");
      fp.printnode(LogFile, n);
      fprintf(LogFile, " (" PRIhollowpcvec ")\n", &v);
    }
    gen g = n->l->g;
    unsigned w = -1;
    if (!v.empty())
      w = Generator[v.begin()->first].w;
    if (w < fp.Weight[g])
      abortprintf(5, "EvalRels: alias %s has weight %u, should have weight at least %u", fp.GeneratorName[g].c_str(), w, fp.Weight[g]);
    
    Epimorphism[g].resize(v.size());
    Epimorphism[g].copy(v);
    vecstack.release(v);
  }

  std::deque<sparsepcvec> itrels;

  for (const auto &n : fp.Relators) {
    node *t;
    for (t = n; t->type == TREL; t = t->l);

    hollowpcvec v = vecstack.fresh();
    v.eval(*this, t);

    for (t = n; t == n || t->type == TREL; t = t->l) {
      hollowpcvec w;
      if (t->type == TREL) {
	w = vecstack.fresh();
	w.eval(*this, t->r);
	w.sub(v);
      } else
	w = v;
      
      w.collect(*this);

      if (Debug >= 2) {
	fprintf(LogFile, "# relation: ");
	fp.printnode(LogFile, n);
	fprintf(LogFile, " (" PRIhollowpcvec ")\n", &w);
      }

#ifdef ASSOCALG
      if (!w.empty() && w.begin()->first == 0)
	abortprintf(3, "Relation does not belong to augmentation ideal");
#endif

      if (!fp.Endomorphisms.empty())
	itrels.push_back(w.getsparse());
    
      m.addrow(w);
      
      if (t->type == TREL)
	vecstack.release(w);
      else
	break;
    }
    vecstack.release(v);
  }

  if (!fp.Endomorphisms.empty()) { // now t is a list of evaluations of rels
    std::vector<sparsepcmat> endos;

    for (const auto &n : fp.Endomorphisms) {
      sparsepcmat phi(NrTotalGens+1,sparsepcvec::bad());

      for (unsigned g = 1; g <= NrTotalGens; g++) {
	hollowpcvec rhs = vecstack.fresh();
	hollowpcvec lhs = vecstack.fresh();
	
	switch (Generator[g].type) {
	case DGEN: case TEMPGEN:
	  {
	    const gen g0 = Generator[g].s;
	    node *m;
	    for (node *t = n;; t = t->l) {
	      if (t->type == TBRACE)
		m = t->r;
	      else
		m = t;
	      if (m->l->g == g0)
		break;
	      if (t->type != TBRACE)
		abortprintf(5, "Could not find generator %u in pc presentation", g);
	    }

	    MapEndo(lhs, *this, Epimorphism[g0], g, phi);
	    rhs.eval(*this, m->r);
	    break;
	  }
	case DCOMM: case TEMPCOMM: // g = [g0,g1]
	  {
	    const gen g0 = Generator[g].g, g1 = Generator[g].h;
	    
	    hollowpcvec v = vecstack.fresh();
	    hollowpcvec w = vecstack.fresh();
#ifdef LIEALG
	    MapEndo(lhs, *this, Comm[g0][g1], g, phi);
	    v.copy(phi[g0]);
	    w.copy(phi[g1]);
	    rhs.liebracket(*this, v, w);
#elif defined(GROUP)
	    MapEndo(lhs, *this, Comm[g0][g1], g, phi);
	    v.copy(phi[g0]);
	    v.mul(*this, phi[g1]); // v = phi[g0]*phi[g1]
	    w.copy(phi[g1]);
	    w.mul(*this, phi[g0]); // w = phi[g1]*phi[g0]
	    rhs.lquo(*this, w, v);
#elif defined(ASSOCALG)
	    MapEndo(lhs, *this, Prod[g0][g1], g, phi);
	    v.copy(phi[g0]);
	    w.copy(phi[g1]);
	    rhs.assocprod(*this, v, w);
#endif	    
	    vecstack.release(w);
	    vecstack.release(v);
	    break;
	  }
	case DPOW: case TEMPPOW: // g = N*g0 or g0^N
	  {
	    const gen g0 = Generator[g].p;
	    MapEndo(lhs, *this, Power[g0], g, phi);
	    
#ifdef GROUP
	    hollowpcvec w = vecstack.fresh();
	    w.copy(phi[g0]);
	    rhs.pow(*this, w, Exponent[g0]);
	    vecstack.release(w);
#else
	    rhs.copy(phi[g0]);
	    rhs.scale(Exponent[g0]);
#endif
	    break;
	  }
	default:
	  abortprintf(5, "Invalid generator definition");
	}

	rhs.sub(lhs);
	vecstack.release(lhs);
	rhs.collect(*this); // this is OK for groups too, it's all in the centre
	phi[g] = rhs.getsparse();
	vecstack.release(rhs);	
      }
      for (unsigned g = 1; g <= NrPcGens; g++)
	phi[g].free();
      phi.erase(phi.begin(), phi.begin()+NrPcGens+1);
      endos.push_back(phi);
      if (Debug >= 2) {
	fprintf(LogFile, "# endomorphism: ");
	fp.printnode(LogFile, n);
	fprintf(LogFile, " (");
	for (unsigned g = NrPcGens+1; g <= NrTotalGens; g++)
	  fprintf(LogFile, "a%u → " PRIsparsepcvec "%s", g, &phi[g-NrPcGens-1], g == NrTotalGens ? ")\n" : "; ");
      }
    }

    while (!itrels.empty()) {
      sparsepcvec t = itrels.front();
      itrels.pop_front();
      
      for (const auto &phi : endos) {
	hollowpcvec h = vecstack.fresh();
	for (const auto &kc : t)
	  h.addmul(kc.second, phi[kc.first-NrPcGens-1]);
	sparsepcvec s = h.getsparse();
	if (Debug >= 2)
	  fprintf(LogFile, "# spun relation: " PRIsparsepcvec " (" PRIsparsepcvec ")\n", &t, &s);
	if (m.addrow(h))
	  s.free();
	else
	  itrels.push_back(s);
	vecstack.release(h);
      }
      
      t.free();
    }

    // free memory
    for (const auto &phi : endos)
      for (auto r : phi)
	r.free();
  }

  TimeStamp("pcpresentation::evalrels()");
}

/* eliminate redundant generators from v; rels is a list of relations
   in the centre, and renumber says how central generators are to be
   renumbered.

   this routine is time-critical. */
void pcpresentation::collecttail(sparsepcvec &v, const matrix &m, std::vector<int> renumber) {
  if (v.empty())
    return;
  
  // first skip over the part of v in degree <= Class
  unsigned writepos, readpos = 0;
  while (v[readpos].first <= NrPcGens) readpos++;

  for (writepos = readpos; v[readpos].first != sparsepcvec::eol; readpos++) {
    int newg = renumber[v[readpos].first];

    if (newg >= 1 && reduced_p(v[readpos].second, Exponent[newg])) {
      v[writepos].first = newg; // renumber in-place
      if (writepos != readpos)
	set(v[writepos].second, v[readpos].second);
      writepos++;
      continue;
    }
    
    if (newg == 0) // shorten v
      continue;

    /* we could optimize further, in case the relation with which to
       replace v[readpos] has length <= readpos-writepos. That doesn't
       seem to be necessary.
    */
  
    sparsepcvec t = m.reducerow(v.window(readpos));
    // then, copy back at correct position and renumber. We're
    // guaranteed that renumber[kc.first] is always >= 1
    v.resize(writepos+t.size());
    auto vi = v.window(writepos).begin();
    for (const auto &kc : t) {
      vi->first = renumber[kc.first];
      set(vi->second, kc.second);
      ++vi;
    }
    vi.markend();
    t.free();
    return;
  }

  if (writepos != readpos) {
    v[writepos].first = sparsepcvec::eol;
    v.resize(writepos);
  }
}

/* quotient the centre by the relations rels */
void pcpresentation::reduce(const matrix &m) {  
  /* renumber[k] = j >= 1 means generator k should be renumbered j.
     renumber[k] = 0 means it should be removed.
     renumber[k] = -1u means that it should be replaced by a relation. */
  std::vector<int> renumber(NrTotalGens + 1);
  unsigned trivialgens = 0;

  for (unsigned k = NrPcGens+1; k <= NrTotalGens; k++) {
    unsigned newk = renumber[k] = k - trivialgens;

    sparsepcvec r = m.getrel(Exponent[newk], k);

    if (Debug >= 2)
#ifdef GROUP
      fprintf(LogFile, "# a%d^" PRIpccoeff " → " PRIsparsepcvec "\n", newk, &Exponent[newk], &r);
#else
      fprintf(LogFile, "# " PRIpccoeff "*a%d → " PRIsparsepcvec "\n", &Exponent[newk], k, &r);
#endif
    
    if (cmp_si(Exponent[newk], 1)) // power relation
      Power[newk] = r;
    else { // eliminate generator k
      trivialgens++;
      if (r.empty())
	renumber[k] = 0;
      else
	renumber[k] = -1; // could be smarter, if Power[newk] is a single term
      r.free();
    }
  }

  unsigned newnrpcgens = NrTotalGens - trivialgens;

  if (Debug >= 2) {
    fprintf(LogFile, "# renumbering:");
    for (unsigned i = 1; i <= NrTotalGens; i++)
      if (renumber[i] != (int) i)
	fprintf(LogFile, " %d→%d", i, renumber[i]);
    fprintf(LogFile, "\n");
  }
    
  /* Modify the torsions: (first, and in decreasing order, though it's unimportant) */
  for (unsigned j = NrTotalGens; j >= 1; j--)
    if (Power[j].allocated())
      collecttail(Power[j], m, renumber);
  
  /*  Modify the epimorphisms: */
  for (unsigned j = 1; j <= fp.NrGens; j++)
    collecttail(Epimorphism[j], m, renumber);
  
  TimeStamp("pcpresentation::reduce1");
  /*  Modify the products: */
  for (unsigned j = 1; j <= NrPcGens; j++)
#ifdef ASSOCALG
    for (unsigned l = 1; l <= NrPcGens; l++)
      collecttail(Prod[j][l], m, renumber);
#else
    for (unsigned l = 1; l < j; l++)
      collecttail(Comm[j][l], m, renumber);
#endif
  TimeStamp("pcpresentation::reduce2");

  /* Let us alter the Generator as well. Recall that dead generators
   * cannot have definition at all. It is only the right of the living
   * ones.
   */
  for (unsigned i = NrPcGens + 1; i <= NrTotalGens; i++)
    if (renumber[i] >= 1)
      Generator[renumber[i]] = Generator[i];

  for (unsigned i = 1; i <= newnrpcgens; i++) /* sanity check */
    if (Generator[i].type & TEMPDEFMASK)
      abortprintf(5, "Generator %d should have been eliminated", i);
  
  for (unsigned i = newnrpcgens+1; i <= NrTotalGens; i++) {
    Exponent[i].clear();
    Annihilator[i].clear();
  }

  /* we could shrink the arrays Generator, Exponent, Annihilator,
     Weight, but it's not worth it */

  /* finally extend the Prod/Comm array, by trivial elements */
#ifdef ASSOCALG
  // we had already allocated it to NrTotalGens. Free the useless part.
  for (unsigned i = newnrpcgens+1; i <= NrTotalGens; i++)
    Prod[0][i].free();
  Prod[0].resize(newnrpcgens+1);
  Prod.resize(newnrpcgens + 1);

  for (unsigned i = 1; i <= newnrpcgens; i++) {
    Prod[i].resize(newnrpcgens+1);
    for (unsigned j = (i > NrPcGens ? 0 : NrPcGens)+1; j <= newnrpcgens; j++)
      Prod[i][j].noalloc();
  }
#else
  Comm.resize(newnrpcgens + 1);

  for (unsigned i = NrPcGens + 1; i <= newnrpcgens; i++) {
    Comm[i].resize(i);
    
    Comm[i][0] = sparsepcvec::bad(); // guard
    for (unsigned j = 1; j < i; j++)
      Comm[i][j].noalloc();
  }
#endif
  
  NrPcGens = newnrpcgens;
  LastGen.resize(Class+1);
  LastGen[Class] = NrPcGens;

  TimeStamp("pcpresentation::reduce()");
}

void pcpresentation::print(FILE *f, bool PrintCompact, bool PrintDefs, bool PrintZeros) const {
  fprintf(f, "<\n");

  std::vector<unsigned> count(Class+1, 0);
  for (unsigned i = 1; i <= NrPcGens; i++)
    count[Generator[i].w]++;
  
  unsigned curclass = 0;
  bool first;
  for (unsigned i = 1; i <= NrPcGens; i++) {
    while (Generator[i].w > curclass) {
      if (curclass++ > 0)
	fprintf(f, ";\n");
      fprintf(f, "# %u generator%s of weight %d:\n", count[curclass], plural(count[curclass]), curclass);
      first = true;
    }
    if (!first)
      fprintf(f, ", ");
    fprintf(f, "a%d", i);
    first = false;
  }
  fprintf(f, " |\n");
  
  fprintf(f, "# The epimorphism:\n");
  for (unsigned i = 1; i <= fp.NrGens; i++) {
    fprintf(f, "# %10s |-->", fp.GeneratorName[i].c_str());
    gen g = Epimorphism[i][0].first;
    if (!Epimorphism[i].empty() && Generator[g].type == DGEN && Generator[g].s == i)
      fprintf(f, ": a%d\n", g);
    else
      fprintf(f, " " PRIsparsepcvec "\n", &Epimorphism[i]);
  }
  if (PrintDefs) {
    fprintf(f, "# The definitions:\n");
    for (unsigned i = 1; i <= NrPcGens; i++) {
      /* we know each element is defined as an iterated multiple of an iterated commutator of generators */
      
      fprintf(f, "#%10s a%d = ", "", i);
      switch (Generator[i].type) {
      case DCOMM:
	fprintf(f, "[a%d,a%d] = ", Generator[i].g, Generator[i].h);
	break;
      case DPOW:
#ifdef LIEALG
	fprintf(f, PRIpccoeff "*a%d = ", &Exponent[i], Generator[i].p);
#else
	fprintf(f, "a%d^" PRIpccoeff " = ", Generator[i].p, &Exponent[i]);
#endif
	break;
      case DGEN:
	fprintf(f, "%s^epi = ", fp.GeneratorName[Generator[i].s].c_str());
	break;
      default:
	abortprintf(5, "Generator %d should have been eliminated", i);
      }

      gen g = i;
      while (Generator[g].type == DPOW) {
#ifdef GROUP
	fprintf(f, "(");
#else
	fprintf(f,PRIpccoeff "*", &Exponent[g]);
#endif
	g = Generator[g].p;
      }
      std::vector<gen> cv;
      while (Generator[g].type == DCOMM) {
	cv.push_back(Generator[g].h);
	g = Generator[g].g;
      }
      fprintf(f, INT_ASSOCALG ? "(" : "[");
      for (;;) {
	if (Generator[g].type != DGEN)
	  abortprintf(5, "Generator %d is not iterated multiple of iterated commutator of generators", i);
	fprintf(f, "%s", fp.GeneratorName[Generator[g].s].c_str());
	if (cv.empty())
	  break;
	g = cv.back();
	cv.pop_back();
	fprintf(f, INT_ASSOCALG ? "*" : ",");
      }
      fprintf(f, INT_ASSOCALG ? ")" : "]");
#ifdef GROUP
      for (g = i; Generator[g].type == DPOW; g = Generator[g].p)
	fprintf(f, "^" PRIpccoeff ")", &Exponent[g]);
#endif
      fprintf(f, "^epimorphism\n");
    }
  }

  first = true;
  fprintf(f, "# The torsion relations:\n");
  for (unsigned i = 1; i <= NrPcGens; i++) {
    if (Jacobson || nz_p(Exponent[i])) {
      if (!first)
	  fprintf(f, ",\n");
      fprintf(f, "%10s", "");
#ifdef GROUP
      fprintf(f, "a%d^" PRIpccoeff, i, &Exponent[i]);
#else
      if (Jacobson)
	fprintf(f, "a%d^p", i);
      else
	fprintf(f, PRIpccoeff "*a%d", &Exponent[i], i);
#endif
      if (Power[i].allocated()) {
	gen g = Power[i][0].first;
	if (!Power[i].empty()) {
	  if (Generator[g].type == DPOW && Generator[g].p == i)
	    fprintf(f, " =: a%d", g);
	  else
	    fprintf(f, " = " PRIsparsepcvec, &Power[i]);
	}
      }
      first = false;
    }
  }
  
  fprintf(f, "%s# The product relations:\n", first ? "" : ",\n");
  first = true;
  for (unsigned j = 1; j <= NrPcGens; j++)
#ifdef ASSOCALG
    for (unsigned i = 1; i <= NrPcGens; i++) {
      if (PrintCompact && (Generator[i].type != DGEN || Generator[j].type == DPOW))
	continue;
      if (!PrintZeros && Prod[j][i].empty())
	continue;

      if (!first)
	fprintf(f, ",\n");
      fprintf(f, "%10sa%d*a%d", "", j, i);
      if (!Prod[j][i].empty()) {
	gen g = Prod[j][i][0].first;
	if (Generator[g].g == j && Generator[g].h == i)
	  fprintf(f, " =: a%d", g);
	else
	  fprintf(f, " = " PRIsparsepcvec, &Prod[j][i]);
      }
      first = false;
    }
#else
    for (unsigned i = 1; i < j; i++) {
      if (PrintCompact && (Generator[i].type != DGEN || Generator[j].type == DPOW))
	continue;
      if (!PrintZeros && Comm[j][i].empty())
	continue;

      if (!first)
	fprintf(f, ",\n");
      fprintf(f, "%10s[a%d,a%d]", "", j, i);
      if (!Comm[j][i].empty()) {
	gen g = Comm[j][i][0].first;
	if (Generator[g].g == j && Generator[g].h == i)
	  fprintf(f, " =: a%d", g);
	else
	  fprintf(f, " = " PRIsparsepcvec, &Comm[j][i]);
      }
      first = false;
    }
#endif
  
  fprintf(f, " >\n");
}

#ifdef GROUP
template<typename V> void PrintGAPVec(FILE *f, const V v) {
  bool first = true;
  for (const auto &kc : v) {
    if (first) first = false; else fprintf(f, "*");
    fprintf(f, "g[%u]^" PRIpccoeff, kc.first, &kc.second);
  }
  if (first)
    fprintf(f, "One(F)");
}
#else
template<typename V> bool PrintGAPVec(FILE *f, const V v, bool first) {
  for (const auto &kc : v) {
    if (first) first = false; else fprintf(f, " + ");
    fprintf(f, PRIpccoeff "*bas[%d]", &kc.second, kc.first);
  }
  return first;
}
#endif

#ifdef LIEALG
// create a GAP-readable file:
// gap> L := ReadAsFunction(filename)();
// will construct a Lie ring L in GAP.
// it has attributes
// - FreeAlgebraOfFpAlgebra, the free algebra with the original generators
// - CanonicalProjection, a function from FreeAlgebraOfFpAlgebra(L) to L
void pcpresentation::printGAP(FILE *f, int level) const {
  fprintf(f, // "L := CallFuncList(function()\n"
	  "\tlocal T, L, bas, epi, src, genimgs, eval;\n\n"
	  "\tLoadPackage(\"liering\");\n\n");

  fprintf(f, "\tsrc := FreeLieRing(Integers,[");
  for (unsigned i = 1; i <= fp.NrGens; i++)
    fprintf(f, "%s\"%s\"", i > 1 ? "," : "", fp.GeneratorName[i].c_str());
  fprintf(f, "]);\n");

  fprintf(f, "\tT := EmptySCTable(%d,0,\"antisymmetric\");\n", NrPcGens);
  for (unsigned j = 1; j <= NrPcGens; j++)
    for (unsigned i = 1; i < j; i++) {
      if (!Comm[j][i].empty()) {
        fprintf(f, "\tSetEntrySCTable(T,%d,%d,[", j, i);
	bool first = true;
	for (const auto &kc : Comm[j][i]) {
	  if (!first) fprintf(f, ",");
	  fprintf(f, PRIpccoeff ",%d", &kc.second, kc.first);
	  first = false;
	}
	fprintf(f, "]);\n");
      }
    }
  fprintf(f, "\tL := LieRingByStructureConstants(ListWithIdenticalEntries(%d,0), T);\n", NrPcGens);
  fprintf(f, "\tbas := Basis(L);\n"
	  "\tepi := NaturalHomomorphismByIdeal(L,LieRingIdeal(L,[");
  bool first = true;
  for (unsigned i = 1; i <= NrPcGens; i++) {
    if (nz_p(Exponent[i])) {
      fprintf(f, "%s-" PRIpccoeff "*bas[%d]", first ? "" : ",\n\t\t", &Exponent[i], i);
      if (Power[i].allocated())
	PrintGAPVec(f, Power[i], false);
      first = false;
    }
  }
  fprintf(f, "],\"basis\"));\n");

  fprintf(f, "\tgenimgs := [");
  for (unsigned i = 1; i <= fp.NrGens; i++) {
    fprintf(f, "%s(", i == 1 ? "" : ",");
    if (PrintGAPVec(f, Epimorphism[i], true))
      fprintf(f, "Zero(L)");
    fprintf(f, ")^epi");
  }
  fprintf(f, "];\n");
  
  fprintf(f, "\tL := Range(epi);\n"
	  "\tSetFreeAlgebraOfFpAlgebra(L,src);\n");

  fprintf(f, "\teval := function(expr)\n"
	  "\t\tif IsBound(expr.var) then\n"
	  "\t\t\treturn genimgs[expr.var];\n"
	  "\t\telse\n"
	  "\t\treturn eval(expr.left)*eval(expr.right);\n"
	  "\t\tfi;\n"
	  "\tend;\n");

  fprintf(f, "\tSetCanonicalProjection(L,function(elm)\n"
	  "\t\tlocal res, i;\n"
	  "\t\tif not elm in src then Error(\"Element \",elm,\" does not belong to free Lie algebra \",src); fi;\n"
	  "\t\telm := elm![1];\n"
	  "\t\tres := Zero(L);\n"
	  "\t\tfor i in [2,4..Length(elm)] do\n"
	  "\t\t\tres := res + elm[i]*eval(elm[i-1]);\n"
	  "\t\tod;\n"
	  "\t\treturn res;\n"
	  "\tend);\n");

  fprintf(f, "\treturn L;\n"
	  // "end,[]);\n"
	  );
}
#elif defined(GROUP)
// create a GAP-readable file:
// gap> G := ReadAsFunction(filename)();
// will construct a group G in GAP.
// it has attributes
// - FreeGroupOfFpGroup, the free group with the original generators
// - EpimorphismFromFreeGroup, a homomorphism from its FreeGroupOfFpGroup(G) to G
// - LowerCentralSeriesOfGroup, the series of subgroups

// print conjugate relation, g_j^{g_i} = ... j and i can be negative, for inverses
inline int signint(int i) { return (i > 0) - (i < 0); }

void printcoeff(FILE *f, const pccoeff &c) {
  char *s = c.get_str(nullptr, 0, 10);
  if (s[0] == '-')
    fprintf(f, "pk");
  fprintf(f, "%s", s);
}

void printconjugate(const pcpresentation &pc, FILE *f, int j, int i) {
  fprintf(f, "\tSetConjugate(c,%d,%d,[", j, i);

  hollowpcvec v = vecstack.fresh();
  pccoeff s;
  s.init();
  s.set_si(-signint(i)); v.mul(pc, abs(i), s);
  s.set_si(signint(j)); v.mul(pc, abs(j), s);
  s.set_si(signint(i)); v.mul(pc, abs(i), s);
  s.clear();

  bool first = true;
  for (const auto &kc : v) {
    if (first) first = false; else fprintf(f, ",");
    fprintf(f, "%u,", kc.first);
    printcoeff(f, kc.second);
  }
  fprintf(f, "]);\n");
  vecstack.release(v);
}

void pcpresentation::printGAP(FILE *f, int level) const {
  fprintf(f, // "G := CallFuncList(function()\n"
	  "\tlocal F, c, g, pk;\n\n");
  if (level == 1)
    fprintf(f, "\tLoadPackage(\"nq\");\n");

#if PCCOEFF_P > 0 // a dirty hack: our printing routines sometimes give negative numbers, we only need positive ones so we replace "-x" by "pk-x" in the output
  fprintf(f, "\tpk := %u^%u;\n", PCCOEFF_P, PCCOEFF_K);
#else
  fprintf(f, "\tpk := 0;\n");
#endif
  
  fprintf(f, "\tF := FreeGroup(IsSyllableWordsFamily,%d,\"a\");\n"
	  "\tg := GeneratorsOfGroup(F);\n", NrPcGens);
  if (level == 1) {
    fprintf(f, "\tc := FromTheLeftCollector(%d);\n", NrPcGens);

    for (unsigned i = 1; i <= NrPcGens; i++)
      if (nz_p(Exponent[i])) {
	fprintf(f, "\tSetRelativeOrder(c,%u," PRIpccoeff ");\n", i, &Exponent[i]);
	fprintf(f, "\tSetPowerNC(c,%u,[", i);
	bool first = true;
	for (const auto &kc : Power[i]) {
	  if (first) first = false; else fprintf(f, ",");
	  fprintf(f, "%u,", kc.first);
	  printcoeff(f, kc.second);
	}
	fprintf(f, "]);\n");
      }
  } else {
    fprintf(f, "\tc := %sCollector(F,[", level == 2 ? "Single" : "Combinatorial");
    for (unsigned i = 1; i <= NrPcGens; i++) {
      if (z_p(Exponent[i]))
	abortprintf(1,"cannot have infinite exponent for a%u in pc group", i);
      else
	fprintf(f, PRIpccoeff ",", &Exponent[i]);
    }
    fprintf(f, "]);\n");
    
    for (unsigned i = 1; i <= NrPcGens; i++) {
      fprintf(f, "\tSetPowerNC(c,%u,", i); PrintGAPVec(f, Power[i]); fprintf(f, ");\n");
    }
  }
  
  for (unsigned j = 1; j <= NrPcGens; j++)
    for (unsigned i = 1; i < j; i++)
      if (!Comm[j][i].empty()) {
	if (level > 1) {
	  fprintf(f, "\tSetConjugateNC(c,%u,%u,g[%u]*", j, i, j); PrintGAPVec(f, Comm[j][i]); fprintf(f, ");\n");
	} else {
	  printconjugate(*this, f, j, i);
	  if (z_p(Exponent[i]))
	    printconjugate(*this, f, j, -i);
	  if (z_p(Exponent[j])) {
	    printconjugate(*this, f, -j, i);
	    if (z_p(Exponent[i]))
	      printconjugate(*this, f, -j, -i);
	  }
	}
      }
  
  fprintf(f, "\tSetFilterObj(c,IsConfluent);\n");
  if (level == 1)
    fprintf(f, "\tUpdatePolycyclicCollector(c);\n"
	    "\tF := PcpGroupByCollector(c);\n");
  else
    fprintf(f, "\tF := GroupByRwsNC(c);\n");
    
  fprintf(f, "\tg := GeneratorsOfGroup(F);\n");
  
  fprintf(f, "\tF!.generatorimages := [");
  for (unsigned i = 1; i <= fp.NrGens; i++) {
    if (i > 1) fprintf(f, ",");
    PrintGAPVec(f, Epimorphism[i]);
  }
  fprintf(f, "];\n");

  fprintf(f, "\tF!.series := [");
  for (unsigned i = 0; i < Class; i++)
    fprintf(f, "Subgroup(F,g{[%u..%u]}),", LastGen[i]+1, NrPcGens);
  fprintf(f, "];\n");

  fprintf(f, "\treturn F;\n"
	  // "end,[]);\n"
	  );
}
#elif defined(ASSOCALG)
// create a GAP-readable file:
// gap> A := ReadAsFunction(filename)();
// will construct an associative algebra A in GAP.
// it has attributes
// - FreeAlgebraOfFpAlgebra, the free algebra with the original generators
// - CanonicalProjection, a function from FreeAlgebraOfFpAlgebra(A) to A
void pcpresentation::printGAP(FILE *f, int level) const {
  fprintf(f, // "A := CallFuncList(function()\n"
	  "\tlocal T, A, bas, epi, src, genimgs, eval;\n\n");

  fprintf(f, "\tsrc := FreeAssociativeAlgebra(Integers,[");
  for (unsigned i = 1; i <= fp.NrGens; i++)
    fprintf(f, "%s\"%s\"", i > 1 ? "," : "", fp.GeneratorName[i].c_str());
  fprintf(f, "]);\n");

  fprintf(f, "\tT := EmptySCTable(%d,0);\n", NrPcGens);
  for (unsigned j = 1; j <= NrPcGens; j++)
    for (unsigned i = 1; i <= NrPcGens; i++) {
      if (!Prod[j][i].empty()) {
        fprintf(f, "\tSetEntrySCTable(T,%d,%d,[", j, i);
	bool first = true;
	for (const auto &kc : Prod[j][i]) {
	  if (!first) fprintf(f, ",");
	  fprintf(f, PRIpccoeff ",%d", &kc.second, kc.first);
	  first = false;
	}
	fprintf(f, "]);\n");
      }
    }
  fprintf(f, "\tA := AlgebraByStructureConstants(Integers, T);\n");
  fprintf(f, "\tError(\"Basis(A) doesn't work yet!\");\n");
  fprintf(f, "\tbas := Basis(A);\n"
	  "\tepi := NaturalHomomorphismByIdeal(A,Ideal(A,[");
  bool first = true;
  for (unsigned i = 1; i <= NrPcGens; i++) {
    if (nz_p(Exponent[i])) {
      fprintf(f, "%s-" PRIpccoeff "*bas[%d]", first ? "" : ",\n\t\t", &Exponent[i], i);
      if (Power[i].allocated())
	PrintGAPVec(f, Power[i], false);
      first = false;
    }
  }
  fprintf(f, "],\"basis\"));\n");

  fprintf(f, "\tgenimgs := [");
  for (unsigned i = 1; i <= fp.NrGens; i++) {
    fprintf(f, "%s(", i == 1 ? "" : ",");
    if (PrintGAPVec(f, Epimorphism[i], true))
      fprintf(f, "Zero(A)");
    fprintf(f, ")^epi");
  }
  fprintf(f, "];\n");
  
  fprintf(f, "\tA := Range(epi);\n"
	  "\tSetFreeAlgebraOfFpAlgebra(A,src);\n");

  fprintf(f, "\teval := function(expr)\n"
	  "\t\tif IsBound(expr.var) then\n"
	  "\t\t\treturn genimgs[expr.var];\n"
	  "\t\telse\n"
	  "\t\treturn eval(expr.left)*eval(expr.right);\n"
	  "\t\tfi;\n"
	  "\tend;\n");

  fprintf(f, "\tSetCanonicalProjection(A,function(elm)\n"
	  "\t\tlocal res, i;\n"
	  "\t\tif not elm in src then Error(\"Element \",elm,\" does not belong to free Lie algebra \",src); fi;\n"
	  "\t\telm := elm![1];\n"
	  "\t\tres := Zero(A);\n"
	  "\t\tfor i in [2,4..Length(elm)] do\n"
	  "\t\t\tres := res + elm[i]*eval(elm[i-1]);\n"
	  "\t\tod;\n"
	  "\t\treturn res;\n"
	  "\tend);\n");

  fprintf(f, "\treturn A;\n"
	  // "end,[]);\n"
	  );
}
#endif
