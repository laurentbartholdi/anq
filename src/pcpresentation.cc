/******************************************************************************
**
**                 Nilpotent Quotient for Lie Rings
** presentation.c                                               Csaba Schneider
**                                                           schcs@math.klte.hu
*/

#include "lienq.h"
#include <vector>

unsigned NrTotalGens;

/* add generator newgen to vector v, and store its definition */
static void AddSingleGenerator(pcpresentation &pc, gpvec &v, deftype def) {
  unsigned l;

  if (v == NULL) {
    v = NewVec(1);
    l = 0;
  } else {
    l = Length(v);
    v = ResizeVec(v, l, l + 1);
  }

  v[l].g = ++NrTotalGens;
  coeff_set_si(v[l].c, 1);
  v[l+1].g = EOW;

  pc.Generator = (deftype *) realloc(pc.Generator, (NrTotalGens + 1) * sizeof(deftype));
  if (pc.Generator == NULL)
    abortprintf(2, "AddSingleGenerator: realloc(Generator) failed");
  
  pc.Generator[NrTotalGens] = def;
}

/* initialize Pc presentation, at class 0. No products or powers are set yet. */
void InitPcPres(pcpresentation &pc, const presentation &pres, bool Graded, bool PAlgebra, coeff &TorsionExp, unsigned NilpotencyClass) {
  /*
  ** The epimorphism maps from the Lie-algebra given by finite presentation to
  ** the nilpotent factor-algebra computed by the LieNQ algorithm.
  */

  /*
  ** We initialize the epimorphism from the finite presentation to the first
  ** (abelian) factor. It is rather trivial at the beginning, actually a
  ** one-to-one map between the two generator set.
*/
  pc.NrPcGens = 0;
  pc.Class = 0;
  pc.Graded = Graded;
  pc.PAlgebra = PAlgebra;
  pc.NilpotencyClass = NilpotencyClass;
  coeff_init_set(pc.TorsionExp, TorsionExp);
  
  pc.Epimorphism = (gpvec *) malloc((pres.NrGens + 1) * sizeof(gpvec));
  if (pc.Epimorphism == NULL)
    abortprintf(2, "InitPcPres: malloc(Epimorphism) failed");
  for (unsigned i = 1; i <= pres.NrGens; i++)
    pc.Epimorphism[i] = NewVec(0);

  pc.Generator = (deftype *) malloc(sizeof(deftype));
  if (pc.Generator == NULL)
    abortprintf(2, "InitPcPres: malloc(Generator) failed");

  /* we initialize the exponents and annihilators of our pc generators */
  pc.Exponent = (coeff *) malloc(sizeof(coeff));
  if (pc.Exponent == NULL)
    abortprintf(2, "InitPcPres: malloc(Exponent) failed");

  pc.Annihilator = (coeff *) malloc((pc.NrPcGens + 1) * sizeof(coeff));
  if (pc.Annihilator == NULL)
    abortprintf(2, "InitPcPres: malloc(Annihilator) failed");

  pc.Power = (gpvec *) malloc(sizeof(gpvec));
  if (pc.Power == NULL)
    abortprintf(2, "InitPcPres: malloc(Power) failed");

  pc.Product = (gpvec **) malloc((pc.NrPcGens + 1) * sizeof(gpvec *));
  if (pc.Product == NULL)
    abortprintf(2, "InitPcPres: malloc(Product) failed");
}

void FreePcPres(pcpresentation &pc, const presentation &pres) {
  for (unsigned i = 1; i <= pc.NrPcGens; i++) {
    if (pc.Power[i] != NULL)
      FreeVec(pc.Power[i]);
    coeff_clear(pc.Exponent[i]);
    coeff_clear(pc.Annihilator[i]);
    for (unsigned j = 1; j < i; j++)
      FreeVec(pc.Product[i][j]);
    free(pc.Product[i]);
  }
  for (unsigned i = 1; i <= pres.NrGens; i++)
    FreeVec(pc.Epimorphism[i]);
  free(pc.Epimorphism);
  free(pc.Power);
  free(pc.Exponent);
  free(pc.Annihilator);
  free(pc.Product);
  free(pc.Generator);
  coeff_clear(pc.TorsionExp);
}

/*
**  The first step is to extend the epimorphism to the next factor.
**  In order to do that we define new generators for the images
**  of the generators of the finite presentation which are not definitions.
*/
void AddNewTails(pcpresentation &pc, const presentation &pres) {
  NrTotalGens = pc.NrPcGens;

  /* inverse lookup tables:
     - is_dgen[i] == (exist g: Generator[g] = {DGEN,i}), so fp generator i is used to define a pc generator or an alias
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

  /* first, add tails to the fp generators. These will have to be eliminated.
     If x is an fp generator of degree d, add a pc generator in degree d,
     in the graded case, and in degree >= d, in the ungraded case.
  */
  for (unsigned i = 1; i <= pres.NrGens; i++) {
    if (is_dgen[i] || pres.Weight[i] >= pc.Class || pc.Graded)
      continue;
    AddSingleGenerator(pc, pc.Epimorphism[i], {.t = DINVALID, .g = i, .h = EOW});
    if (Debug >= 2)
      fprintf(LogFile, "# added tail a%d to epimorphic image of %s\n", NrTotalGens, pres.GeneratorName[i].c_str());
  }

  /* now add new generators ("tails") to powers and commutators.

     In mode "TorsionExp > 0", we use as basis
     generators of the form N*[ai,aj,...] with ai,aj,... of degree 1.
     In mode "TorsionExp == 0", we force N=1.

     This means that in mode "TorsionExp > 0" we favour powers, so we
     put them last; while in mode "TorsionExp == 0" we avoid them, so
     we put them first.
  */
  for (int pass = 0; pass < 2; pass++) {
    /* for all pc generators g with Exponent[g]!=0, add a tail to
       Power[g], unless:
       - g is defined as a power
       - we're in graded, torsion mode (so producing a (Z/TorsionExp)[t]-algebra) and g has degree < Class-1
    */
    if (pass == pc.PAlgebra) {
      for (unsigned i = 1; i <= pc.NrPcGens; i++) {
	if (is_dpow[i] || !coeff_nz_p(pc.Exponent[i]))
	  continue;
	if (pc.Graded && (!pc.PAlgebra || pc.Generator[i].w+1 != pc.Class))
	  continue;
	AddSingleGenerator(pc, pc.Power[i], {.t = (pc.PAlgebra ? DPOW : DINVALID), .g = i, .h = EOW, .w = pc.Class, .cw = pc.Generator[i].cw});
	if (Debug >= 2)
	  fprintf(LogFile, "# added tail a%d to non-defining torsion generator a%d\n", NrTotalGens, i);
      }
    }

    if (pass == !pc.PAlgebra) {
      /* for all non-power pc generators g of weight <=Class-k and all
	 defining pc generators h of weight k, with g > h, and such
	 that [g,h] is not defining, add a tail to Product[g][h].

	 all other tails will be computed in Tails() out of these:
	 - if h is not defining, using Jacobi or Z-linearity;
	 - if g is a power, using Z-linearity */
      for (unsigned i = 1; i <= pc.NrPcGens; i++) {
	if (pc.Generator[i].t != DGEN)
	  continue;
	for (unsigned j = i+1; j <= pc.NrPcGens; j++) {
	  if (is_dcomm[j][i])
	    continue;
	  if (pc.Generator[j].t == DPOW)
	    continue;
	  unsigned totalweight = pc.Generator[i].w+pc.Generator[j].w;
	  if (totalweight > pc.Class || (pc.Graded && totalweight != pc.Class))
	    continue;
	  unsigned totalcweight = pc.Generator[i].cw + pc.Generator[j].cw;
	  if (totalcweight > pc.NilpotencyClass)
	    continue;
	  
	  AddSingleGenerator(pc, pc.Product[j][i], {.t = DCOMM, .g = j, .h = i, .w = pc.Class, .cw = totalcweight});
	  if (Debug >= 2)
	    fprintf(LogFile, "# added tail a%d to non-defining commutator [a%d, a%d]\n", NrTotalGens, j, i);
	}
      }
    }
  }

  /* finally, add new pc generators for the new fp generators.
  */
  for (unsigned i = 1; i <= pres.NrGens; i++) {
    if (pres.Weight[i] != pc.Class)
      continue;
    AddSingleGenerator(pc, pc.Epimorphism[i], {.t = DGEN, .g = i, .h = EOW, .w = pc.Class, .cw = 1});
    if (Debug >= 2)
      fprintf(LogFile, "# added tail a%d as epimorphic image of %s\n", NrTotalGens, pres.GeneratorName[i].c_str());
  }

  /*
  **  Extend the arrays of exponents, commutators etc. to the
  **  necessary size.  Let's define the newly introduced generators to
  **  be central i.e.  All of their product relations will be trivial
  **  and also they have coefficients 0.
  */

  pc.Exponent = (coeff *) realloc(pc.Exponent, (NrTotalGens + 1) * sizeof(coeff));
  if (pc.Exponent == NULL)
    abortprintf(2, "AddNewTails: realloc(Exponent) failed");
  for (unsigned i = pc.NrPcGens + 1; i <= NrTotalGens; i++)
    coeff_init_set(pc.Exponent[i], pc.TorsionExp);

  pc.Annihilator = (coeff *) realloc(pc.Annihilator, (NrTotalGens + 1) * sizeof(coeff));
  if (pc.Annihilator == NULL)
    abortprintf(2, "AddNewTails: realloc(Annihilator) failed");
  for (unsigned i = pc.NrPcGens + 1; i <= NrTotalGens; i++)
    coeff_init_set_si(pc.Annihilator[i], 0);

  pc.Power = (gpvec *) realloc(pc.Power, (NrTotalGens + 1) * sizeof(gpvec));
  if (pc.Power == NULL)
    abortprintf(2, "AddNewTails: realloc(Power) failed");
  for (unsigned i = pc.NrPcGens + 1; i <= NrTotalGens; i++)
    pc.Power[i] = NULL;

  /* The Product array is not extended yet, because anyways it won't be used.
     we'll extend it later, in ReducePcPres */
    
  TimeStamp("AddNewTails()");
}

/* eliminate redundant generators from v; rels is a list of relations
   in the centre, and renumber says how central generators are to be
   renumbered. */

/* This is time-critical. It can be optimized in various ways:
   -- g is a central generator, so we can skip the beginning if we ever
      have to call Diff
   -- Matrix is in Hermite normal form -- we could put it in Smith NF, maybe,
      and then the collection would be simpler?
   -- often w will have only 1 or 2 non-trivial entries, in which case the
      operation can be done in-place
*/

static void EliminateTrivialGenerators(pcpresentation &pc, const relmatrix &rels, gpvec &v, int renumber[]) {
  bool copied = false;
  unsigned pos = 0;

  for (; v[pos].g != EOW;) {
    int newg = renumber[v[pos].g];
    if (newg >= 1) {
      v[pos].g = newg;
      pos++;
    } else {
      constgpvec rel = rels[-newg];
      gpvec temp = FreshVec();
      Diff(temp, v+pos+1, v[pos].c, rel+1);
      if (!copied) { /* we should make sure we have enough space */
	gpvec newv = NewVec(NrTotalGens);
	v[pos].g = EOW; /* cut original p at this position, copy to newv */
	Copy(newv, v);
	v[pos].g = rel->g; /* put it back, so we can free correctly v */
	FreeVec(v);
	v = newv;
      }
      Copy(v+pos, temp);
      PopVec();
      copied = true;
    }
  }
  if (copied)
    v = ResizeVec(v, NrTotalGens, pos);
  ShrinkCollect(pc, v);
}

/* quotient the centre by the relations rels */
void ReducePcPres(pcpresentation &pc, const presentation &pres, const relmatrix &rels) {
  unsigned trivialgens = 0;

  if (Debug >= 2) {
    fprintf(LogFile, "# relations matrix:\n");
    for (constgpvec r : rels) {
      fprintf(LogFile, "# "); PrintVec(LogFile, r); fprintf(LogFile, "\n");
    }
  }

  /* renumber[k] = j >= 1 means generator k should be renumbered j.
     renumber[k] = j <= 0 means generator k should be eliminated using row j */
  int *renumber = new int[NrTotalGens + 1];

  for (unsigned k = 1, i = 0; k <= NrTotalGens; k++) {
    unsigned newk = renumber[k] = k - trivialgens;
    if (i == rels.size() || k != rels[i]->g) /* no relation for k, remains */
      continue;

    if (coeff_cmp_si(rels[i]->c, 1)) { /* k is torsion, nontrivial */
      coeff_set(pc.Exponent[newk], rels[i]->c);
      pc.Power[newk] = NewVec(Length(rels[i]+1));
      Neg(pc.Power[newk], rels[i]+1);
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
    if (pc.Power[j] != NULL)
      EliminateTrivialGenerators(pc, rels, pc.Power[j], renumber);
  
  /*  Modify the epimorphisms: */
  for (unsigned j = 1; j <= pres.NrGens; j++)
    EliminateTrivialGenerators(pc, rels, pc.Epimorphism[j], renumber);
  
  /*  Modify the products: */
  for (unsigned j = 1; j <= pc.NrPcGens; j++)
    for (unsigned l = 1; l < j; l++)
      EliminateTrivialGenerators(pc, rels, pc.Product[j][l], renumber);

  /* Let us alter the Generator as well. Recall that dead generator cannot
  have definition at all. It is only the right of the living ones. */
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

  /* finally extend the Product array, by trivial elements */
  pc.Product = (gpvec **) realloc(pc.Product, (newnrpcgens + 1) * sizeof(gpvec *));
  if (pc.Product == NULL)
    abortprintf(2, "ReducePcPres: realloc(Product) failed");

  for (unsigned i = pc.NrPcGens + 1; i <= newnrpcgens; i++) {
    pc.Product[i] = (gpvec *) malloc(i * sizeof(gpvec));
    if (pc.Product[i] == NULL)
      abortprintf(2, "ReducePcPres: realloc(Product[%d]) failed", i);

    for (unsigned j = 1; j < i; j++)
      pc.Product[i][j] = NewVec(0);
  }
  
  TimeStamp("ReducePcPres()");

  pc.NrPcGens = newnrpcgens;
}
