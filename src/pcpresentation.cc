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
  pc.Generator[0] = {.t = DINVALID};

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
typedef enum { TAIL, CONSISTENCY } tail_mode;
// when mode=TAIL, we're computing the tail of [f,[g,h]]
// when mode=CONSISTENCY, we're checking associativity
// the code is the same, the debugging messages are different.
static hollowcvec tail_assoc(const pcpresentation &pc, gen f, gen g, gen h, tail_mode mode) {
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

  if (Debug >= 2) {
    if (mode == TAIL)
      fprintf(LogFile, "# tail: [a%d,a%d] *= ", f, pc.Comm[g][h].front()->first);
    else
      fprintf(LogFile, "# consistency: ");
    fprintf(LogFile, "associator(a%d,a%d,a%d) = ", f, g, h);
    PrintVec(LogFile, rhs);
    fprintf(LogFile, "\n");
  }
  return rhs;
}

// return fresh tail of power relation. Here g is torsion, pc.Exponent[g]=N>0.
// if f>g: it's f*g^N \ f*g*g^(N-1)
// if f=g: it's f^N*f \ f*f^N
// if f<g: it's g^N*f \ g^(N-1)*f*g*[g,f]
static hollowcvec tail_pow(const pcpresentation &pc, gen f, gen g, tail_mode mode) {
  hollowcvec lhs = vecstack.fresh();
  hollowcvec rhs = vecstack.fresh();
  
  if (f > g) { /* f*g^N = f*g*g^(N-1) */
    coeff_set_si(lhs[f], 1);
    lhs.mul(pc, pc.Power[g]);

    coeff_set_si(rhs[f], 1);
    rhs.mul(pc, g);
    coeff c;
    coeff_init(c);
    coeff_add_si(c, pc.Exponent[g], -1); // maybe can do in 1 go? !!!
    rhs.mul(pc, g, c);
    coeff_clear(c);

    if (Debug >= 2) {
      if (mode == TAIL)
	fprintf(LogFile, "# tail: [a%d,a%d] *= ", f, g);
      else
	fprintf(LogFile, "# consistency: associator(a%d^(N-1),a%d,a%d) = ", f, f, g);
    }
  } else if (f < g) { /* g^N*f = g^(N-1)*f*g*[g,f] */
    lhs.copysorted(pc.Power[g]);
    lhs.mul(pc, f);


    coeff_add_si(rhs[g], pc.Exponent[g], -1);
    rhs.mul(pc, f);
    rhs.mul(pc, g);
    rhs.mul(pc, pc.Comm[g][f]);

    if (Debug >= 2) {
      if (mode == TAIL)
	fprintf(LogFile, "# tail: [a%d,a%d] *= ", f, g);
      else
	fprintf(LogFile, "# consistency: associator(a%d,a%d,a%d^(N-1)) = ", g, f, f);
    }
  } else { /* f*f^N = f^N*f */
    lhs.copysorted(pc.Power[f]);
    lhs.mul(pc, f);

    coeff_set_si(rhs[f], 1);
    rhs.mul(pc, pc.Power[f]);

    if (Debug >= 2) {
      if (mode == TAIL)
	fprintf(LogFile, "# tail: [a%d,a%d] *= ", f, g);
      else
	fprintf(LogFile, "# consistency: commutator(a%d,a%d^N) = ", g, f);
    }
  }
  lhs.sub(rhs);
  vecstack.pop(rhs);

  if (Debug >= 2) {
    PrintVec(LogFile, lhs);
    fprintf(LogFile, "\n");
  }
  return lhs;
}
#endif

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
  for (node *n : pres.Aliases) {
    gen g = n->cont.bin.l->cont.g;
    if (is_dgen[g])
      abortprintf(3, "(At least) two definitions for generator %d", g);
    is_dgen[g] = true;
  }
    
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
    AddSingleGenerator(pc, pc.Epimorphism[i], {.t = DINVALID, .g = i});
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
	if (pc.Graded && (!pc.PAlgebra || pc.Generator[i].w+1 != pc.Class))
	  continue;
	AddSingleGenerator(pc, pc.Power[i], {.t = (pc.PAlgebra ? DPOW : DINVALID), .g = i, .w = pc.Class, .cw = pc.Generator[i].cw});
	if (Debug >= 2)
	  fprintf(LogFile, "# added tail a%d to non-defining torsion generator a%d\n", NrTotalGens, i);
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
      for (unsigned weight = 2; weight <= pc.Class; weight++) {
	if (pc.Graded && weight != pc.Class)
	  continue;
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
	    unsigned totalcweight = pc.Generator[i].cw + pc.Generator[j].cw;
	    if (totalcweight > pc.NilpotencyClass)
	      continue;
	  
	    AddSingleGenerator(pc, pc.Comm[j][i], {.t = (weight == pc.Class ? DCOMM : DINVALID), .g = j, .h = i, .w = pc.Class, .cw = totalcweight});
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
      unsigned totalweight = pc.Generator[i].w+pc.Generator[j].w;
      if (totalweight > pc.Class || (pc.Graded && totalweight != pc.Class))
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
	if (Debug >= 2) {
	  fprintf(LogFile, "# tail: [a%d,a%d] = [a%d,[a%d,a%d]] = ", j, i, j, g, h);
	}
      } else if (pc.Generator[i].t == DPOW) { /* ai = N*g */
	gen g = pc.Generator[i].g;
	tail.addmul(pc.Exponent[g], pc.Comm[j][g]);
	tail.liecollect(pc);
	if (Debug >= 2) {
	  fprintf(LogFile, "# tail: [a%d,a%d] = ", j, i);
	  coeff_out_str(LogFile, pc.Exponent[g]);
	  fprintf(LogFile, "*[a%d,a%d] = ", j, g);
	}
      } else if (pc.Generator[j].t == DPOW) { /* aj = N*g */
	gen g = pc.Generator[j].g;
	if (g > i)
	  tail.addmul(pc.Exponent[g], pc.Comm[g][i]);
	else if (g < i)
	  tail.submul(pc.Exponent[g], pc.Comm[i][g]);
	tail.liecollect(pc);
	if (Debug >= 2) {
	  fprintf(LogFile, "# tail: [a%d,a%d] = ", j, i);
	  coeff_out_str(LogFile, pc.Exponent[g]);
	  fprintf(LogFile, "*[a%d,a%d] = ", g, i);
	}
      } else
	abortprintf(5, "AddTails: unknown definition for [a%d,a%d]", j, i);
      
      if (Debug >= 2) {
	PrintVec(LogFile, tail);
	fprintf(LogFile, "\n");
      }

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
       * - if aj is defined as g^N, compute [aj,ai] *= !!!
       */
      hollowcvec tail;

      if (pc.Generator[i].t == DCOMM) /* ai = [g,h] */
	tail = tail_assoc(pc, j, pc.Generator[i].g, pc.Generator[i].h, TAIL);
      else if (pc.Generator[i].t == DPOW) /* ai = g^N */
	tail = tail_pow(pc, j, pc.Generator[i].g, TAIL);
      else if (pc.Generator[j].t == DPOW) /* aj = g^N */
	tail = tail_pow(pc, i, pc.Generator[j].g, TAIL);
	// !!! check sign
      else
	abortprintf(5, "AddTails: unknown definition for [a%d,a%d]", j, i);

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
#ifdef LIEALG
void Consistency(const pcpresentation &pc) {
  // check Jacobi identity
  for (unsigned i = 1; i <= pc.NrPcGens; i++) {
    if (pc.Generator[i].t != DGEN)
      continue;

    for (unsigned j = i + 1; j <= pc.NrPcGens; j++)
      for (unsigned k = j + 1; k <= pc.NrPcGens; k++) {
	unsigned totalweight = pc.Generator[i].w + pc.Generator[j].w + pc.Generator[k].w;
	if (totalweight > pc.Class || (pc.Graded && totalweight != pc.Class))
	  continue;
	
	hollowcvec t = vecstack.fresh();
	t.lie3bracket(pc, i, j, k, true);
	t.lie3bracket(pc, j, k, i, true);
	t.lie3bracket(pc, k, i, j, true);
	t.liecollect(pc);

	if (Debug >= 2) {
	  fprintf(LogFile, "# consistency: jacobi(a%d,a%d,a%d) = ", i, j, k);
	  PrintVec(LogFile, t);
	  fprintf(LogFile, "\n");
	}

	QueueInRelMatrix(t);	
	vecstack.pop(t);
      }
  }
  
  coeff annihilator, unit;
  coeff_init(annihilator);
  coeff_init(unit); // unused

  // check torsion relations
  for (unsigned i = 1; i <= pc.NrPcGens; i++)
    if (coeff_nz_p(pc.Exponent[i])) {
      /* if N*v = 0 in our ring, and we have a power relation A*g = w,
       * enforce (N/A)*w = 0
       */
      hollowcvec t = vecstack.fresh();
  
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
      
      QueueInRelMatrix(t);
      vecstack.pop(t);

      for (unsigned j = 1; j <= pc.NrPcGens; j++) {
	unsigned totalweight = pc.Generator[i].w + pc.Generator[j].w;
	if (totalweight > pc.Class || (pc.Graded && totalweight != pc.Class))
	  continue;

	/* enforce N*[a,b] = [N*a,b] if N is the order of a */

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

	if (Debug >= 2) {
	  fprintf(LogFile, "# consistency: ");
	  coeff_out_str(LogFile, pc.Exponent[i]);
	  fprintf(LogFile, "*[a%d,a%d]-[", i, j);
	  coeff_out_str(LogFile, pc.Exponent[i]);
	  fprintf(LogFile, "*a%d,a%d] = ", i, j);
	  PrintVec(LogFile, t);
	  fprintf(LogFile, "\n");
	}

	QueueInRelMatrix(t);
	vecstack.pop(t);
      }
    }

  coeff_clear(unit);
  coeff_clear(annihilator);

  FlushQueue();
  
  TimeStamp("Consistency()");
}
#else
void Consistency(const pcpresentation &pc) {
  // check associativity
  for (unsigned i = 1; i <= pc.NrPcGens; i++) {
    if (pc.Generator[i].t != DGEN)
      continue;

    for (unsigned j = i + 1; j <= pc.NrPcGens; j++)
      for (unsigned k = j + 1; k <= pc.NrPcGens; k++) {
	unsigned totalweight = pc.Generator[i].w + pc.Generator[j].w + pc.Generator[k].w;
	if (totalweight > pc.Class || (pc.Graded && totalweight != pc.Class))
	  continue;
	
	hollowcvec tail = tail_assoc(pc, k, j, i, CONSISTENCY);

	QueueInRelMatrix(tail);	
	vecstack.pop(tail);
      }
  }
  
  coeff annihilator, unit;
  coeff_init(annihilator);
  coeff_init(unit); // unused

  // check torsion relations
  for (unsigned i = 1; i <= pc.NrPcGens; i++)
    if (coeff_nz_p(pc.Exponent[i])) {
      /* if the group's exponent is given (by the torsion in the
	 coefficients), impose a power relation */
      hollowcvec t = vecstack.fresh();
      coeff_unit_annihilator(unit, annihilator, pc.Exponent[i]);

      hollowcvec u = vecstack.fresh();
      u.copysorted(pc.Power[i]);      
      t.pow(pc, u, annihilator);
      vecstack.pop(u);
      
      if (Debug >= 2) {
	fprintf(LogFile, "# consistency: ");
	fprintf(LogFile, "(a%d^", i);
	coeff_out_str(LogFile, pc.Exponent[i]);
	fprintf(LogFile, ")^");
	coeff_out_str(LogFile, annihilator);
	fprintf(LogFile, " = ");
	PrintVec(LogFile, t);
	fprintf(LogFile, "\n");
      }
      
      QueueInRelMatrix(t);
      vecstack.pop(t);

      for (unsigned j = 1; j <= pc.NrPcGens; j++) {
	unsigned totalweight = pc.Generator[i].w + pc.Generator[j].w;
	if (totalweight > pc.Class || (pc.Graded && totalweight != pc.Class))
	  continue;

	/* enforce a^N*b = a^(N-1)*(a*b) or a*b^N = (a*b)*b^(N-1) */

	hollowcvec tail = tail_pow(pc, j, i, CONSISTENCY);
	QueueInRelMatrix(tail);
	vecstack.pop(tail);
      }
    }

  coeff_clear(unit);
  coeff_clear(annihilator);

  FlushQueue();
  
  TimeStamp("Consistency()");
}
#endif

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
      fprintf(LogFile, " ("); PrintVec(LogFile, v); fprintf(LogFile, ")\n");
    }

    if (!pres.Endomorphisms.empty())
      itrels.push_back(v.getsparse());
    
    AddToRelMatrix(v);

    vecstack.pop(v);
  }

  if (!pres.Endomorphisms.empty()) { // now t is a list of evaluations of rels
    std::vector<relmatrix> endos;

    for (auto n : pres.Endomorphisms) {
      std::vector<sparsecvec> phi(NrTotalGens+1,badsparsecvec);
      for (unsigned g = 1; g <= NrTotalGens; g++) {
	switch (pc.Generator[g].t) {
	case DGEN:
	  {
	    node *m;
	    for (node *t = n;; t = t->cont.bin.r) {
	      if (t->type == TBRACE)
		m = t->cont.bin.l;
	      else
		m = t;
	      if (m->cont.bin.l->cont.g == pc.Generator[g].g)
		break;
	      if (t->type != TBRACE)
		abortprintf(5, "Could not find generator %u in pc presentation", g);
	    }

	    hollowcvec v = vecstack.fresh();

	    v.eval(pc, m->cont.bin.r);
	    phi[g] = v.getsparse();

	    vecstack.pop(v);
	    break;
	  }
	case DCOMM: // g = [g0,g1]
	  {
	    hollowcvec c = vecstack.fresh();
	    hollowcvec v = vecstack.fresh();
	    hollowcvec w = vecstack.fresh();
#ifdef LIEALG
	    v.copysorted(phi[pc.Generator[g].g]);
	    w.copysorted(phi[pc.Generator[g].h]);
	    c.liebracket(pc, v, w);
#else
	    c.copysorted(phi[pc.Generator[g].g]);
	    w.copysorted(phi[pc.Generator[g].h]);
	    v.copy(c);
	    v.mul(pc, w); // v = phi[g0]*phi[g1]
	    w.mul(pc, v); // w = phi[g1]*phi[g0]
	    c.clear();
	    c.lquo(pc, w, v);
#endif	    
	    vecstack.pop(w);
	    vecstack.pop(v);
	    phi[g] = c.getsparse();
	    vecstack.pop(c);
	    break;
	  }
	case DPOW: // g = N*g0 or g0^N
	  {
	    hollowcvec v = vecstack.fresh();
#ifdef LIEALG
	    v.copysorted(phi[pc.Generator[g].g]);
	    v.mul(pc.Exponent[pc.Generator[g].g]);
#else
	    hollowcvec w = vecstack.fresh();
	    w.copysorted(phi[pc.Generator[g].g]);
	    v.pow(pc, w, pc.Exponent[pc.Generator[g].g]);
	    vecstack.pop(w);
#endif
	    phi[g] = v.getsparse();
	    vecstack.pop(v);
	  }
	  break;
	}
      }
      for (unsigned g = 1; g <= pc.NrPcGens; g++)
	phi[g].free();
      phi.erase(phi.begin(), phi.begin()+pc.NrPcGens+1);
      endos.push_back(phi);
      if (Debug >= 2) {
	fprintf(LogFile, "# endomorphism: ");
	PrintNode(LogFile, pres, n);
	fprintf(LogFile, " (");
	for (unsigned g = pc.NrPcGens+1; g <= NrTotalGens; g++) {
	  PrintVec(LogFile, phi[g-pc.NrPcGens-1]);
	  fprintf(LogFile, g == NrTotalGens ? ")\n" : "; ");
	}
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
	if (Debug >= 2) {
	  fprintf(LogFile, "# spun relation: ");
	  PrintVec(LogFile, t);
	  fprintf(LogFile, " ("); PrintVec(LogFile, s); fprintf(LogFile, ")\n");
	}
	if (AddToRelMatrix(h))
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
   renumbered. */

/* !!! This is time-critical. It can be optimized in various ways:
   -- g is a central generator, so we can skip the beginning if we ever
      have to call Diff
   -- Matrix is in Hermite normal form -- we could put it in Smith NF, maybe,
      and then the collection would be simpler?
   -- often w will have only 1 or 2 non-trivial entries, in which case the
      operation can be done in-place
   -- Matrix could be renumbered once rather than at each time
*/

static void EliminateTrivialGenerators(pcpresentation &pc, const relmatrix &rels, sparsecvec &v, int renumber[]) {
  
  hollowcvec t = vecstack.fresh();
  t.copysorted(v);
  v.free();

  // first, eliminate
  for (auto kc : t) {
    int newg = renumber[kc.first];
    if (newg < 1) {
      t.submul(kc.second, rels[-newg].window(1));
      coeff_set_si(kc.second, 0);
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
  for (auto q = v.begin(); q != v.end(); q++) {
    int newg = renumber[q->first];
    if (newg >= 1)
      q->first = newg;
    else {
      // !!! here we could be smart by examining rels[-newg].
      // if it's a single term, we're actually shortening v
      // if it's a sum of two terms, replace one by the other

      // we restart, with a hollow vector
      t = vecstack.fresh();
      t.copysorted(q.tail()); // we must collect from here on
      for (auto kc : t) {
	int newg = renumber[kc.first];
	if (newg >= 1) {
	  coeff_set(t[kc.first], t[newg]);
	  coeff_set_si(t[newg], 0);
	} else
	  t.submul(kc.second, rels[-newg]);
      }
      q.markend(); // add back the first part of the vector, which is unaffected
      t.add(v);
      t.liecollect(pc); // liecollect is OK, since we're in the centre

      v.free();
      v = t.getsparse();
      vecstack.pop(t);
      return;
    }
  }
#endif
}

/* quotient the centre by the relations rels */
void ReducePcPres(pcpresentation &pc, const fppresentation &pres, const relmatrix &rels) {
  unsigned trivialgens = 0;

  if (Debug >= 2) {
    fprintf(LogFile, "# relations matrix:\n");
    for (const sparsecvec r : rels) {
      fprintf(LogFile, "# "); PrintVec(LogFile, r); fprintf(LogFile, "\n");
    }
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
      if (pc.Generator[i].t == DINVALID)
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
