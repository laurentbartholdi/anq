/******************************************************************************
**
**                 Nilpotent Quotient for Lie Rings
** presentation.c                                               Csaba Schneider
**                                                           schcs@math.klte.hu
*/

#include "nq.h"
#include <vector>
#include <deque>

// during extension of pc presentation, NrTotalGens = new NrPcGens.
unsigned NrTotalGens;

/* add generator newgen to vector v, and store its definition */
static void AddSingleGenerator(pcpresentation &pc, sparsecvec &v, deftype def) {
  unsigned len = v.size();
  v.resize(len+1);
  v[len].first = ++NrTotalGens;
  coeff_set_si(v[len].second, 1);
  v.truncate(len+1);

  pc.Generator = (deftype *) realloc(pc.Generator, (NrTotalGens + 1) * sizeof(deftype));
  if (pc.Generator == nullptr)
    abortprintf(2, "AddSingleGenerator: realloc(Generator) failed");
  
  pc.Generator[NrTotalGens] = def;
}

/* initialize Pc presentation, at class 0. No products or powers are set yet. */
void InitPcPres(pcpresentation &pc, const fppresentation &pres) {
  pc.NrPcGens = 0;
  pc.Class = 0;

  coeff_init(pc.TorsionExp);

  pc.Epimorphism = (sparsecvec *) malloc((pres.NrGens + 1) * sizeof(sparsecvec));
  if (pc.Epimorphism == NULL)
    abortprintf(2, "InitPcPres: malloc(Epimorphism) failed");
  pc.Epimorphism[0] = badsparsecvec; // guard
  for (unsigned i = 1; i <= pres.NrGens; i++)
    pc.Epimorphism[i].alloc(0);
  
  pc.Generator = (deftype *) malloc(sizeof(deftype));
  if (pc.Generator == NULL)
    abortprintf(2, "InitPcPres: malloc(Generator) failed");
  pc.Generator[0] = {.t = (gendeftype) -1};

  /* we initialize the exponents and annihilators of our pc generators */
  pc.Exponent = (coeff *) malloc(sizeof(coeff));
  if (pc.Exponent == NULL)
    abortprintf(2, "InitPcPres: malloc(Exponent) failed");

  pc.Annihilator = (coeff *) malloc((pc.NrPcGens + 1) * sizeof(coeff));
  if (pc.Annihilator == NULL)
    abortprintf(2, "InitPcPres: malloc(Annihilator) failed");

  pc.Power = (sparsecvec *) malloc(sizeof(sparsecvec));
  if (pc.Power == NULL)
    abortprintf(2, "InitPcPres: malloc(Power) failed");
  pc.Power[0] = badsparsecvec; // guard

  pc.Comm = (sparsecvec **) malloc((pc.NrPcGens + 1) * sizeof(sparsecvec *));
  if (pc.Comm == NULL)
    abortprintf(2, "InitPcPres: malloc(Comm) failed");

  TimeStamp("InitPcPres()");  
}

void FreePcPres(pcpresentation &pc, const fppresentation &pres) {
  for (unsigned i = 1; i <= pc.NrPcGens; i++) {
    if (pc.Power[i].allocated())
      pc.Power[i].free();
    coeff_clear(pc.Exponent[i]);
    coeff_clear(pc.Annihilator[i]);
    for (unsigned j = 1; j < i; j++)
      pc.Comm[i][j].free();
    free(pc.Comm[i]);
  }
  for (unsigned i = 1; i <= pres.NrGens; i++)
    pc.Epimorphism[i].free();
  free(pc.Epimorphism);
  free(pc.Power);
  free(pc.Exponent);
  free(pc.Annihilator);
  free(pc.Comm);
  free(pc.Generator);
  coeff_clear(pc.TorsionExp);
}

#ifdef GROUP
// return fresh tail to (f*g)*h / f*(g*h), with f > g > h
static hollowcvec tail_assoc(const pcpresentation &pc, gen f, gen g, gen h) {
  hollowcvec rhs = vecstack.fresh();
  hollowcvec lhs = vecstack.fresh();
  
  coeff_set_si(lhs[f], 1);
  lhs.mul(pc, h);
  lhs.mul(pc, g);
  lhs.mul(pc, pc.Comm[g][h]); // lhs = f*(g*h) = f*h*g*[g,h]
  
  coeff_set_si(rhs[f], 1);
  rhs.mul(pc, g);
  rhs.mul(pc, h); // rhs = (f*g)*h

  rhs.sub(lhs);
  vecstack.pop(lhs);

  return rhs;
}

// return fresh tail of power relation. Here g is torsion, pc.Exponent[g]=N>0.
// if f>g: it's f*g^N \ f*g*g^(N-1)
// if f=g: it's f^N*f \ f*f^N
// if f<g: it's g^N*f \ g^(N-1)*f*g*[g,f]
static hollowcvec tail_pow(const pcpresentation &pc, gen f, gen g) {
  hollowcvec rhs = vecstack.fresh();
  hollowcvec lhs = vecstack.fresh();
  
  if (f > g) { /* f*g*g^(N-1) = f*g^N */
    coeff_set_si(lhs[f], 1);
    lhs.mul(pc, g);
    coeff_add_si(rhs[g], pc.Exponent[g], -1);
    lhs.mul(pc, rhs);
    rhs.clear();
    
    coeff_set_si(rhs[f], 1);
    rhs.mul(pc, pc.Power[g]);
  } else if (f < g) { /* g^N*f = g^(N-1)*f*g*[g,f] */
    lhs.copysorted(pc.Power[g]);
    lhs.mul(pc, f);

    coeff_add_si(rhs[g], pc.Exponent[g], -1);
    rhs.mul(pc, f);
    rhs.mul(pc, g);
    rhs.mul(pc, pc.Comm[g][f]);
  } else { /* f*f^N = f^N*f */
    lhs.copysorted(pc.Power[f]);
    lhs.mul(pc, f);

    coeff_set_si(rhs[f], 1);
    rhs.mul(pc, pc.Power[f]);
  }
  rhs.sub(lhs);
  vecstack.pop(lhs);

  return rhs;
}
#endif

// should [i,j] receive a tail?
inline bool isgoodweight_comm(const pcpresentation &pc, int i, int j) {
  unsigned totalweight = pc.Generator[i].w + pc.Generator[j].w;

  if (totalweight > pc.Class)
    return false;

  if (pc.Graded && totalweight != pc.Class)
    return false;

  unsigned totalcweight = pc.Generator[i].cw + pc.Generator[j].cw;

  if (totalcweight > pc.NilpotencyClass)
    return false;
  
  if (pc.Metabelian && pc.Generator[i].cw > 1 && pc.Generator[j].cw > 1)
    return false;

  return true;  
}

/* The first step, to extend a pc presentation one class ahead, is to
 * define new generators for all relations which are not definitions,
 * the so-called "tails".
 */
unsigned AddTails(pcpresentation &pc, const fppresentation &pres) {
  NrTotalGens = pc.NrPcGens;

  /* inverse lookup tables:
     - is_dgen[i] == (exist g: Generator[g] = {DGEN,i}), so fp generator i is used to define a pc generator, or is an alias
     is_dpow[i] == (exist g: Generator[g] = {DPOW,i}), so ai^Exponent[i] = ag
     is_dcomm[i][j] == (exist g: Generator[g] = {DCOMM,i,j}), so [ai,aj] = ag
  */
  std::vector<bool> is_dgen(pres.NrGens+1,false);
  std::vector<bool> is_dpow(pc.NrPcGens+1,false);
  std::vector<std::vector<bool>> is_dcomm(pc.NrPcGens+1);

  /* first mark aliases */
  for (auto n : pres.Aliases)
    is_dgen[n->cont.bin.l->cont.g] = true;
    
  for (unsigned i = 1; i <= pc.NrPcGens; i++) {
    is_dcomm[i] = std::vector<bool>(i,false);

    switch (pc.Generator[i].t) {
    case DCOMM:
      is_dcomm[pc.Generator[i].g][pc.Generator[i].h] = true;
      break;
    case DGEN:
      is_dgen[pc.Generator[i].g] = true;
      break;
    case DPOW:
      is_dpow[pc.Generator[i].g] = true;
      break;
    default:
      abortprintf(4, "Generator %d should have been eliminated", i);
    }
  }

  /* first, add tails to the non-defining fp generators. These will
     have to be eliminated later.

     If x is an fp generator of degree d, add a pc generator in degree
     d, in the graded case, and in degree >= d, in the ungraded case.
  */
  for (unsigned i = 1; i <= pres.NrGens; i++) {
    if (is_dgen[i] || pres.Weight[i] >= pc.Class || pc.Graded)
      continue;
    AddSingleGenerator(pc, pc.Epimorphism[i], {.t = TEMPGEN, .g = i, .w = pc.Class, .cw = 1});
    if (Debug >= 2)
      fprintf(LogFile, "# added tail a%d to epimorphic image of %s\n", NrTotalGens, pres.GeneratorName[i].c_str());
  }

  /* now add new generators ("tails") to powers and commutators.

     In mode "TorsionExp > 0", we will use as basis of the algebra/group
     generators of the form N*[ai,aj,...] with ai,aj,... of degree 1.
     In mode "TorsionExp == 0", we force N=1.

     This means that in mode "TorsionExp > 0", equivalently
     pc.PAlgebra is set, we favour powers, so we put commutators on
     pass 0 and powers on pass 1; while in mode "TorsionExp == 0" we
     avoid them, so we put powers on pass 0 and commutators on pass 1.
  */
  for (int pass = 0; pass < 2; pass++) {
    if (pass == pc.PAlgebra) {
      /* for all pc generators g with Exponent[g]!=0, add a tail to
	 Power[g], unless:
	 - g is defined as a power
	 - we're in graded, torsion mode (so producing a (Z/TorsionExp)[t]-algebra) and g has degree < Class-1
      */
      for (unsigned i = 1; i <= pc.NrPcGens; i++) {
	if (is_dpow[i] || !coeff_nz_p(pc.Exponent[i]))
	  continue;
	unsigned targetweight = (pc.Jennings ? pc.Generator[i].w*coeff_base : pc.Generator[i].w+1);
	if (targetweight > pc.Class || (pc.Graded && targetweight != pc.Class))
	  continue;
	if (pc.Graded && !pc.PAlgebra)
	  continue;
	AddSingleGenerator(pc, pc.Power[i], {.t = (pc.PAlgebra ? DPOW : TEMPPOW), .g = i, .w = pc.Class, .cw = pc.Generator[i].cw});
	if (Debug >= 2)
	  fprintf(LogFile, "# added tail a%d to non-defining torsion a%d^" PRIcoeff "\n", NrTotalGens, i, &pc.Exponent[i]);
      }
    }

    if (pass == !pc.PAlgebra) {
      /* for all non-power pc generators g of weight <=Class-k and all
	 defining pc generators h of weight k, with g > h, and such
	 that [g,h] is not defining, add a tail to Comm[g][h].

	 all other tails will be computed in Tails() out of these:
	 - if h is not defining, using Jacobi or Z-linearity;
	 - if g is a power, using Z-linearity.

	 we have to first add weights of low class, and then higher,
	 to be sure that the generator that will be kept after consistency
	 and relations are imposed is a valid defining generator (namely,
	 of totalweight = pc.Class). */
      for (unsigned weight = (pc.Graded ? pc.Class : 2); weight <= pc.Class; weight++) {
	for (unsigned i = 1; i <= pc.NrPcGens; i++) {
	  if (pc.Generator[i].t != DGEN)
	    continue;
	  for (unsigned j = i+1; j <= pc.NrPcGens; j++) {
	    if (is_dcomm[j][i])
	      continue;
	    if (pc.Generator[j].t == DPOW)
	      continue;
	    unsigned totalweight = pc.Generator[i].w+pc.Generator[j].w;
	    if (totalweight != weight)
	      continue;

	    if (!isgoodweight_comm(pc, i, j))
	      continue;
	    
	    AddSingleGenerator(pc, pc.Comm[j][i], {.t = (weight == pc.Class ? DCOMM : TEMPCOMM), .g = j, .h = i, .w = pc.Class, .cw = pc.Generator[i].cw+pc.Generator[j].cw});
	    if (Debug >= 2)
	      fprintf(LogFile, "# added tail a%d to non-defining commutator [a%d,a%d]\n", NrTotalGens, j, i);
	  }
	}
      }
    }
  }

  /* finally, add new pc generators for the new fp generators.
   */
  for (unsigned i = 1; i <= pres.NrGens; i++) {
    if (pres.Weight[i] != pc.Class || is_dgen[i])
      continue;
    AddSingleGenerator(pc, pc.Epimorphism[i], {.t = DGEN, .g = i, .w = pc.Class, .cw = 1});
    if (Debug >= 2)
      fprintf(LogFile, "# added tail a%d as epimorphic image of %s\n", NrTotalGens, pres.GeneratorName[i].c_str());
  }

  /* Extend the arrays of exponents, commutators etc. to the necessary
   *  size.  Let's define the newly introduced generators to be
   *  central i.e.  All of their product relations will be trivial and
   *  also they have coefficients 0.
   */
  pc.Exponent = (coeff *) realloc(pc.Exponent, (NrTotalGens + 1) * sizeof(coeff));
  if (pc.Exponent == NULL)
    abortprintf(2, "AddTails: realloc(Exponent) failed");
  for (unsigned i = pc.NrPcGens + 1; i <= NrTotalGens; i++)
    coeff_init_set(pc.Exponent[i], pc.TorsionExp);

  pc.Annihilator = (coeff *) realloc(pc.Annihilator, (NrTotalGens + 1) * sizeof(coeff));
  if (pc.Annihilator == NULL)
    abortprintf(2, "AddTails: realloc(Annihilator) failed");
  for (unsigned i = pc.NrPcGens + 1; i <= NrTotalGens; i++)
    coeff_init_set_si(pc.Annihilator[i], 0);

  pc.Power = (sparsecvec *) realloc(pc.Power, (NrTotalGens + 1) * sizeof(sparsecvec));
  if (pc.Power == NULL)
    abortprintf(2, "AddTails: realloc(Power) failed");
  for (unsigned i = pc.NrPcGens + 1; i <= NrTotalGens; i++)
    pc.Power[i].noalloc();

  /* The Comm array is not extended yet, because anyways it won't
     be used.  we'll extend it later, in ReducePcPres */

  // set the size of vectors in the vector stack, since we'll soon
  // have to do some collecting
  vecstack.setsize(NrTotalGens);
  if (Debug >= 2)
    fprintf(LogFile, "# added new tails, total number of generators is %u\n", NrTotalGens);

  /* Some of the newly introduced generators strictly depend on one
   * another hence we can compute them inductively.
   */
  for (unsigned j = pc.NrPcGens; j >= 1; j--) {
    for (unsigned i = 1; i < j; i++) {
      if (!isgoodweight_comm(pc, i, j))
	continue;
	  
      if (pc.Generator[i].t == DGEN && pc.Generator[j].t != DPOW) /* nothing to do, [aj,ai] is a defining generator */
	continue;

#ifdef LIEALG
      /* compute the correct tail for [aj,ai]: in Lie algebra,
       * - if ai is defined as [g,h], compute [aj,ai] = [aj,g,h]-[aj,h,g]
       * - if ai is defined as N*g, compute [aj,ai] = N*[aj,g]
       * - if aj is defined as N*g, compute [aj,ai] = N*[g,ai] or -N*[ai,g].
       */
      hollowcvec tail = vecstack.fresh();

      if (pc.Generator[i].t == DCOMM) { /* ai = [g,h] */
	gen g = pc.Generator[i].g, h = pc.Generator[i].h;
	tail.lie3bracket(pc, j, g, h, true); // +[[aj,g],h]
	tail.lie3bracket(pc, j, h, g, false); // -[[aj,h],g]
	tail.liecollect(pc);

	if (Debug >= 2)
	  fprintf(LogFile, "# tail: [a%d,a%d] = [a%d,[a%d,a%d]] = " PRIhollowcvec "\n", j, i, j, g, h, &tail);
      } else if (pc.Generator[i].t == DPOW) { /* ai = N*g */
	gen g = pc.Generator[i].g;
	tail.addmul(pc.Exponent[g], pc.Comm[j][g]);
	tail.liecollect(pc);

	if (Debug >= 2)
	  fprintf(LogFile, "# tail: [a%d,a%d] = " PRIcoeff "*[a%d,a%d] = " PRIhollowcvec "\n", j, i, &pc.Exponent[g], j, g, &tail);
      } else if (pc.Generator[j].t == DPOW) { /* aj = N*g */
	gen g = pc.Generator[j].g;
	if (g > i)
	  tail.addmul(pc.Exponent[g], pc.Comm[g][i]);
	else if (g < i)
	  tail.submul(pc.Exponent[g], pc.Comm[i][g]);
	tail.liecollect(pc);

	if (Debug >= 2)
	  fprintf(LogFile, "# tail: [a%d,a%d] = " PRIcoeff "*[a%d,a%d] = " PRIhollowcvec "\n", j, i, &pc.Exponent[g], g, i, &tail);
      } else
	abortprintf(4, "AddTails: unknown definition for [a%d,a%d]", j, i);
      
      unsigned len = 0;
      auto tp = tail.begin();
      for (auto kc : pc.Comm[j][i]) {
	if (kc.first != (*tp).first || coeff_cmp(kc.second,(*tp).second))
	  abortprintf(5, "AddTails: adjustment to tail of [a%d,a%d] doesn't lie in centre", j, i);
	len++;
	tp++;
      }

      if (tp != tail.end()) {
	pc.Comm[j][i].resize(len, tail.size());
	pc.Comm[j][i].window(len).copy(tp, tail.end());
      }
      vecstack.pop(tail);
#else      
      /* compute the correct tail for [aj,ai]: in groups,
       * - if ai is defined as [g,h], compute [aj,ai] *= (aj(gh))^-1 * (ajg)h
       * - if ai is defined as g^N, compute [aj,ai] *= (aj g^N)^-1 * (ajg)g^(N-1)
       * - if aj is defined as g^N, compute [aj,ai] *= (g^N a_i)^-1 * (g^(N-1)*(g*a_i))
       */
      hollowcvec tail;

      if (pc.Generator[i].t == DCOMM) { /* ai = [g,h] */
	tail = tail_assoc(pc, j, pc.Generator[i].g, pc.Generator[i].h);

	if (Debug >= 2)
	  fprintf(LogFile, "# tail: [a%d,a%d] = [a%d,[a%d,a%d]] *= " PRIhollowcvec "\n", j, i, j, pc.Generator[i].g, pc.Generator[i].h, &tail);
      } else if (pc.Generator[i].t == DPOW) { /* ai = g^N */
	tail = tail_pow(pc, j, pc.Generator[i].g);
	tail.neg();

	if (Debug >= 2)
	  fprintf(LogFile, "# tail: [a%d,a%d] = [a%d,a%d^" PRIcoeff "] *= " PRIhollowcvec "\n", j, i, j, pc.Generator[i].g, &pc.Exponent[pc.Generator[i].g], &tail);
      } else if (pc.Generator[j].t == DPOW) { /* aj = g^N */
	tail = tail_pow(pc, i, pc.Generator[j].g);

	if (Debug >= 2)
	  fprintf(LogFile, "# tail: [a%d,a%d] = [a%d^" PRIcoeff ",a%d] *= " PRIhollowcvec "\n", j, i, pc.Generator[j].g, &pc.Exponent[pc.Generator[j].g], i, &tail);
      } else
	abortprintf(4, "AddTails: unknown definition for [a%d,a%d]", j, i);

      if (!tail.empty()) {
	if (tail.front()->first <= pc.NrPcGens)
	  abortprintf(5, "Addtails: adjustment to tail of [a%d,a%d] doesn't lie in centre", j, i);

	unsigned len = pc.Comm[j][i].size();
	
	pc.Comm[j][i].resize(len, len+tail.size());
	pc.Comm[j][i].window(len).copy(tail);
      }
      vecstack.pop(tail);
#endif
    }
  }
  
  TimeStamp("AddTails()");

  return NrTotalGens - pc.NrPcGens;
}

/* check consistency of pc presentation, and deduce relations to
 * impose on centre
 */
void Consistency(const pcpresentation &pc) {
  // check Jacobi identity
  for (unsigned i = 1; i <= pc.NrPcGens; i++) {
    if (pc.Generator[i].t != DGEN)
      continue;

    unsigned commi = (pc.Generator[i].cw > 1);
    
    for (unsigned j = i + 1; j <= pc.NrPcGens; j++) {
      unsigned commij = commi + (pc.Generator[j].cw > 1);
      if (pc.Metabelian && commij >= 2)
	continue;
      
      for (unsigned k = j + 1; k <= pc.NrPcGens; k++) {
	unsigned totalweight = pc.Generator[i].w + pc.Generator[j].w + pc.Generator[k].w;
	if (totalweight > pc.Class || (pc.Graded && totalweight != pc.Class))
	  continue;
	
	if (pc.Metabelian && commij + (pc.Generator[k].cw > 1) >= 2)
	  continue;
	
#ifdef LIEALG
	hollowcvec t = vecstack.fresh();
	t.lie3bracket(pc, i, j, k, true);
	t.lie3bracket(pc, j, k, i, true);
	t.lie3bracket(pc, k, i, j, true);
	t.liecollect(pc);

	if (Debug >= 2)
	  fprintf(LogFile, "# consistency: jacobi(a%d,a%d,a%d) = " PRIhollowcvec "\n", i, j, k, &t);
#else
	hollowcvec t = tail_assoc(pc, k, j, i);

	if (Debug >= 2)
	  fprintf(LogFile, "# consistency: associator(a%d,a%d,a%d) = " PRIhollowcvec "\n", k, j, i, &t);
#endif
	QueueInMatrix(t);	
	vecstack.pop(t);
      }
    }
  }
  
  coeff annihilator, unit;
  coeff_init(annihilator);
  coeff_init(unit); // unused

  // check torsion relations
  for (unsigned i = 1; i <= pc.NrPcGens; i++)
    if (coeff_nz_p(pc.Exponent[i])) {
      /* if N*v = 0 in our ring, and we have a power relation A*g = w,
       * enforce (N/A)*w = 0.
       * if the group's exponent is given (by the torsion in the
       * ccoefficients), impose a power relation.
       */
      hollowcvec t = vecstack.fresh();
  
      coeff_unit_annihilator(unit, annihilator, pc.Exponent[i]);
#ifdef LIEALG
      t.addmul(annihilator, pc.Power[i]);
      t.liecollect(pc);
  
      if (Debug >= 2)
	fprintf(LogFile, "# consistency: " PRIcoeff "*" PRIcoeff "*a%d = " PRIhollowcvec "\n", &annihilator, &pc.Exponent[i], i, &t);
#else
      hollowcvec u = vecstack.fresh();
      u.copysorted(pc.Power[i]);      
      t.pow(pc, u, annihilator);
      vecstack.pop(u);
      
      if (Debug >= 2)
	fprintf(LogFile, "# consistency: (a%d^" PRIcoeff ")^" PRIcoeff " = " PRIhollowcvec "\n", i, &pc.Exponent[i], &annihilator, &t);
#endif      
      QueueInMatrix(t);
      vecstack.pop(t);

      for (unsigned j = 1; j <= pc.NrPcGens; j++) {
	if (!isgoodweight_comm(pc, i, j))
	  continue;

	/* enforce N*[a,b] = [N*a,b] if N is the order of a; or
	 * a^N*b = a^(N-1)*(a*b) or a*b^N = (a*b)*b^(N-1) in groups
	 */
#ifdef LIEALG
	hollowcvec t = vecstack.fresh();
  
	for (auto kc : pc.Power[i]) {
	  gen g = kc.first;
	  if (g > pc.NrPcGens)
	    break;
	  if (g > j)
	    t.submul(kc.second, pc.Comm[g][j]);
	  else if (g < j)
	    t.addmul(kc.second, pc.Comm[j][g]);
	}

	if (i > j)
	  t.addmul(pc.Exponent[i], pc.Comm[i][j]);
	else if (i < j)
	  t.submul(pc.Exponent[i], pc.Comm[j][i]);
	t.liecollect(pc);

	if (Debug >= 2)
	  fprintf(LogFile, "# consistency: " PRIcoeff "*[a%d,a%d]-[" PRIcoeff "*a%d,a%d] = " PRIhollowcvec "\n", &pc.Exponent[i], i, j, &pc.Exponent[i], i, j, &t);
#else
	hollowcvec t = tail_pow(pc, j, i);

	if (Debug >= 2)
	  fprintf(LogFile, "# consistency: associator(a%d,a%d,a%d^(N-1)) = " PRIhollowcvec "\n", j, i, i, &t);
#endif	
	QueueInMatrix(t);
	vecstack.pop(t);
      }
    }

  coeff_clear(unit);
  coeff_clear(annihilator);

  TimeStamp("Consistency()");
}

// compute result = src^phi, except for the symbol g in src
void MapEndo(hollowcvec &result, const pcpresentation &pc, sparsecvec src, gen avoid, const sparsecmat &phi) {
  for (auto kc : src) {
    if (kc.first == avoid)
      continue;
#ifdef LIEALG
    result.addmul(kc.second, phi[kc.first]);
#else
    hollowcvec p = vecstack.fresh();
    p.copysorted(phi[kc.first]);
    result.pow(pc, p, kc.second);
    vecstack.pop(p);
#endif
  }
}

// Evaluate all relations in pc, ship them to Matrix
void EvalAllRel(const pcpresentation &pc, const fppresentation &pres) {
  for (auto n : pres.Aliases) {
    hollowcvec v = vecstack.fresh();
    v.eval(pc, n->cont.bin.r);
    v.liecollect(pc);

    if (Debug >= 2) {
      fprintf(LogFile, "# aliasing relation: ");
      PrintNode(LogFile, pres, n);
      fprintf(LogFile, " (" PRIhollowcvec ")\n", &v);
    }
    gen g = n->cont.bin.l->cont.g;
    pc.Epimorphism[g].resize(v.size());
    pc.Epimorphism[g].copy(v);
    vecstack.pop(v);
  }

  std::deque<sparsecvec> itrels;

  for (auto n : pres.Relators) {
    hollowcvec v = vecstack.fresh();
    v.eval(pc, n);
    v.liecollect(pc);

    if (Debug >= 2) {
      fprintf(LogFile, "# relation: ");
      PrintNode(LogFile, pres, n);
      fprintf(LogFile, " (" PRIhollowcvec ")\n", &v);
    }

    if (!pres.Endomorphisms.empty())
      itrels.push_back(v.getsparse());
    
    AddToMatrix(v);

    vecstack.pop(v);
  }

  if (!pres.Endomorphisms.empty()) { // now t is a list of evaluations of rels
    std::vector<sparsecmat> endos;

    for (auto n : pres.Endomorphisms) {
      sparsecmat phi(NrTotalGens+1,badsparsecvec);

      for (unsigned g = 1; g <= NrTotalGens; g++) {
	hollowcvec rhs = vecstack.fresh();
	hollowcvec lhs = vecstack.fresh();
	const gen g0 = pc.Generator[g].g;
	
	switch (pc.Generator[g].t) {
	case DGEN: case TEMPGEN:
	  {
	    node *m;
	    for (node *t = n;; t = t->cont.bin.l) {
	      if (t->type == TBRACE)
		m = t->cont.bin.r;
	      else
		m = t;
	      if (m->cont.bin.l->cont.g == g0)
		break;
	      if (t->type != TBRACE)
		abortprintf(5, "Could not find generator %u in pc presentation", g);
	    }

	    MapEndo(lhs, pc, pc.Epimorphism[g0], g, phi);
	    rhs.eval(pc, m->cont.bin.r);
	    break;
	  }
	case DCOMM: case TEMPCOMM: // g = [g0,g1]
	  {
	    const gen g1 = pc.Generator[g].h;
	    
	    MapEndo(lhs, pc, pc.Comm[g0][g1], g, phi);
	    
	    hollowcvec v = vecstack.fresh();
	    hollowcvec w = vecstack.fresh();
#ifdef LIEALG
	    v.copysorted(phi[g0]);
	    w.copysorted(phi[g1]);
	    rhs.liebracket(pc, v, w);
#else
	    v.copysorted(phi[g0]);
	    v.mul(pc, phi[g1]); // v = phi[g0]*phi[g1]
	    w.copysorted(phi[g1]);
	    w.mul(pc, phi[g0]); // w = phi[g1]*phi[g0]
	    rhs.lquo(pc, w, v);
#endif	    
	    vecstack.pop(w);
	    vecstack.pop(v);
	    break;
	  }
	case DPOW: case TEMPPOW: // g = N*g0 or g0^N
	  {
	    MapEndo(lhs, pc, pc.Power[g0], g, phi);
	    
#ifdef LIEALG
	    rhs.copysorted(phi[g0]);
	    rhs.mul(pc.Exponent[g0]);
#else
	    hollowcvec w = vecstack.fresh();
	    w.copysorted(phi[g0]);
	    rhs.pow(pc, w, pc.Exponent[g0]);
	    vecstack.pop(w);
#endif
	    break;
	  }
	}

	rhs.sub(lhs);
	vecstack.pop(lhs);
	rhs.liecollect(pc); // this is OK for groups too, it's all in the centre
	phi[g] = rhs.getsparse();
	vecstack.pop(rhs);	
      }
      for (unsigned g = 1; g <= pc.NrPcGens; g++)
	phi[g].free();
      phi.erase(phi.begin(), phi.begin()+pc.NrPcGens+1);
      endos.push_back(phi);
      if (Debug >= 2) {
	fprintf(LogFile, "# endomorphism: ");
	PrintNode(LogFile, pres, n);
	fprintf(LogFile, " (");
	for (unsigned g = pc.NrPcGens+1; g <= NrTotalGens; g++)
	  fprintf(LogFile, "a%u → " PRIsparsecvec "%s", g, &phi[g-pc.NrPcGens-1], g == NrTotalGens ? ")\n" : "; ");
      }
    }

    while (!itrels.empty()) {
      sparsecvec t = itrels.front();
      itrels.pop_front();
      
      for (auto phi : endos) {
	hollowcvec h = vecstack.fresh();
	for (auto kc : t)
	  h.addmul(kc.second, phi[kc.first-pc.NrPcGens-1]);
	sparsecvec s = h.getsparse();
	if (Debug >= 2)
	  fprintf(LogFile, "# spun relation: " PRIsparsecvec " (" PRIsparsecvec ")\n", &t, &s);
	if (AddToMatrix(h))
	  s.free();
	else
	  itrels.push_back(s);
	vecstack.pop(h);
      }
      
      t.free();
    }

    // free memory
    for (auto phi : endos)
      for (auto r : phi)
	r.free();
  }

  TimeStamp("EvalAllRel()");
}

/* eliminate redundant generators from v; rels is a list of relations
   in the centre, and renumber says how central generators are to be
   renumbered.

   @@@ this is time-critical. */
static void EliminateTrivialGenerators(pcpresentation &pc, const sparsecmat &rels, sparsecvec &v, int renumber[]) {
  
  hollowcvec t = vecstack.fresh();
  t.copysorted(v);
  v.free();

  // first, eliminate !!! we should call MatrixReduce on the tail of v
  for (auto kc : t) {
    int newg = renumber[kc.first];
    if (newg < 1) {
      // we can't do that, because kc.second will get modified in the process
      // (it would be OK if we could subtract in descending direction)
      //t.submul(kc.second, rels[-newg]);
      t.submul(kc.second, rels[-newg].window(1));
      coeff_zero(t[kc.first]);
    }
  }

  // then, renumber. We're guaranteed that renumber[kc.first] is >= 1
  hollowcvec u = vecstack.fresh();
  for (auto kc : t)
    coeff_set(u[renumber[kc.first]], kc.second);
  u.liecollect(pc); /* only collect the exponents in the abelian part,
		       same for Lie algebra and group */

  v = u.getsparse();

  vecstack.pop(u);
  vecstack.pop(t);

#if 0 // premature optimization
  for (auto q = v.upper_bound(pc.NrPcGens); q != v.end(); q++) {
    int newg = renumber[q->first];
    if (newg >= 1)
      q->first = newg; // renumber in-place
    else {
      const sparsecvec rel = rels[-newg].window(1);
      if (rel.empty()) {
	// we're actually removing an entry from q
	q--;
      } else if (rel.window(1).empty()) {
	// we're replacing an entry with another
	q->first = rel[0].first;
	coeff_neg(q->second, q->second);
	coeff_mul(q->second, rel[0].second, q->second);
      } else {
	// now we should make a copy of the vector, and work with the hollow one
#error copy code above
      }
    }
  }
#endif
}

/* quotient the centre by the relations rels */
void ReducePcPres(pcpresentation &pc, const fppresentation &pres, const sparsecmat &rels) {
  unsigned trivialgens = 0;

  if (Debug >= 2) {
    fprintf(LogFile, "# relations matrix:\n");
    for (const sparsecvec r : rels)
      fprintf(LogFile, "# " PRIsparsecvec "\n", &r);
  }

  /* renumber[k] = j >= 1 means generator k should be renumbered j.
     renumber[k] = j <= 0 means generator k should be eliminated using row j */
  int *renumber = new int[NrTotalGens + 1];

  for (unsigned k = 1, i = 0; k <= NrTotalGens; k++) {
    unsigned newk = renumber[k] = k - trivialgens;
    if (i == rels.size() || k != rels[i][0].first) /* no relation for k, remains */
      continue;

    if (coeff_cmp_si(rels[i][0].second, 1)) { /* k is torsion, nontrivial */
      coeff_set(pc.Exponent[newk], rels[i][0].second);
      const sparsecvec tail = rels[i].window(1);
      pc.Power[newk].alloc(tail.size());
      neg(pc.Power[newk], tail); // negate N*ai+... = 0 to N*ai = -(...)
    } else { /* k is trivial, and will be eliminated */
      trivialgens++;
      renumber[k] = -i; /* mark as trivial */
    }
    i++;
  }
  unsigned newnrpcgens = NrTotalGens - trivialgens;

  if (Debug >= 2) {
    fprintf(LogFile, "# renumbering:");
    for (unsigned i = 1; i <= NrTotalGens; i++)
      if (renumber[i] != (int) i)
	fprintf(LogFile, " %d→%d", i, renumber[i]);
    fprintf(LogFile, "\n");
  }
    
  /* Modify the torsions first, in decreasing order, since they're needed
     for Collect */
  for (unsigned j = NrTotalGens; j >= 1; j--)
    if (pc.Power[j].allocated())
      EliminateTrivialGenerators(pc, rels, pc.Power[j], renumber);
  
  /*  Modify the epimorphisms: */
  for (unsigned j = 1; j <= pres.NrGens; j++)
    EliminateTrivialGenerators(pc, rels, pc.Epimorphism[j], renumber);
  
  /*  Modify the products: */
  for (unsigned j = 1; j <= pc.NrPcGens; j++)
    for (unsigned l = 1; l < j; l++)
      EliminateTrivialGenerators(pc, rels, pc.Comm[j][l], renumber);

  /* Let us alter the Generator as well. Recall that dead generators
   * cannot have definition at all. It is only the right of the living
   * ones.
   */
  for (unsigned i = pc.NrPcGens + 1; i <= NrTotalGens; i++)
    if (renumber[i] >= 1)
      pc.Generator[renumber[i]] = pc.Generator[i];

  if (!pc.PAlgebra) /* sanity check */
    for (unsigned i = 1; i <= newnrpcgens; i++)
      if (pc.Generator[i].t & TEMPMASK)
	abortprintf(5, "Generator %d should have been eliminated", i);
  
  for (unsigned i = newnrpcgens+1; i <= NrTotalGens; i++) {
    coeff_clear(pc.Exponent[i]);
    coeff_clear(pc.Annihilator[i]);
  }

  delete[] renumber;
  /* we could shrink the arrays Generator, Exponent, Annihilator,
     Weight, but it's not worth it */

  /* finally extend the Comm array, by trivial elements */
  pc.Comm = (sparsecvec **) realloc(pc.Comm, (newnrpcgens + 1) * sizeof(sparsecvec *));
  if (pc.Comm == nullptr)
    abortprintf(2, "ReducePcPres: realloc(Comm) failed");

  for (unsigned i = pc.NrPcGens + 1; i <= newnrpcgens; i++) {
    pc.Comm[i] = (sparsecvec *) malloc(i * sizeof(sparsecvec));
    if (pc.Comm[i] == nullptr)
      abortprintf(2, "ReducePcPres: realloc(Comm[%d]) failed", i);

    pc.Comm[i][0] = badsparsecvec; // guard
    for (unsigned j = 1; j < i; j++)
      pc.Comm[i][j].noalloc();
  }
  
  TimeStamp("ReducePcPres()");

  pc.NrPcGens = newnrpcgens;
}
