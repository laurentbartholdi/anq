/******************************************************************************
**
**                 Nilpotent Quotient for Lie Rings
** presentation.c                                               Csaba Schneider
**                                                           schcs@math.klte.hu
*/

#include "lienq.h"
#include <vector>

gpvec **Product,  *Power, *Epimorphism;
coeff *Exponent, *Annihilator;

deftype *Definition;

unsigned *Weight, Class, NrPcGens, NrTotalGens;

/* add generator newgen to vector v, and store its definition */
static void AddSingleGenerator(gpvec &v, deftype def) {
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

  Definition = (deftype *) realloc(Definition, (NrTotalGens + 1) * sizeof(deftype));
  if (Definition == NULL)
    abortprintf(2, "AddSingleGenerator: realloc(Definition) failed");
  
  Definition[NrTotalGens] = def;
}

/* initialize Pc presentation, at class 0. No products or powers are set yet. */
void InitPcPres(presentation &Pres) {
  /*
  ** The epimorphism maps from the Lie-algebra given by finite presentation to
  ** the nilpotent factor-algebra computed by the LieNQ algorithm.
  */

  /*
  ** We initialize the epimorphism from the finite presentation to the first
  ** (abelian) factor. It is rather trivial at the beginning, actually a
  ** one-to-one map between the two generator set.
*/
  NrPcGens = 0;
  Class = 0;
  
  Epimorphism = (gpvec *) malloc((Pres.NrGens + 1) * sizeof(gpvec));
  if (Epimorphism == NULL)
    abortprintf(2, "InitPcPres: malloc(Epimorphism) failed");
  for (unsigned i = 1; i <= Pres.NrGens; i++)
    Epimorphism[i] = NewVec(0);

  Definition = (deftype *) malloc(sizeof(deftype));
  if (Definition == NULL)
    abortprintf(2, "InitPcPres: malloc(Definition) failed");

  Weight = (unsigned *) malloc(sizeof(unsigned));
  if (Weight == NULL)
    abortprintf(2, "InitPcPres: malloc(Weight) failed");

  /* we initialize the exponents and annihilators of our pc generators */
  Exponent = (coeff *) malloc(sizeof(coeff));
  if (Exponent == NULL)
    abortprintf(2, "InitPcPres: malloc(Exponent) failed");

  Annihilator = (coeff *) malloc((NrPcGens + 1) * sizeof(coeff));
  if (Annihilator == NULL)
    abortprintf(2, "InitPcPres: malloc(Annihilator) failed");

  Power = (gpvec *) malloc(sizeof(gpvec));
  if (Power == NULL)
    abortprintf(2, "InitPcPres: malloc(Power) failed");

  Product = (gpvec **) malloc((NrPcGens + 1) * sizeof(gpvec *));
  if (Product == NULL)
    abortprintf(2, "InitPcPres: malloc(Product) failed");
}

void FreePcPres(presentation &Pres) {
  for (unsigned i = 1; i <= NrPcGens; i++) {
    if (Power[i] != NULL)
      FreeVec(Power[i]);
    coeff_clear(Exponent[i]);
    coeff_clear(Annihilator[i]);
    for (unsigned j = 1; j < i; j++)
      FreeVec(Product[i][j]);
    free(Product[i]);
  }
  for (unsigned i = 1; i <= Pres.NrGens; i++)
    FreeVec(Epimorphism[i]);
  free(Epimorphism);
  free(Power);
  free(Exponent);
  free(Annihilator);
  free(Product);
  free(Definition);
  free(Weight);
}

/*
**  The first step is to extend the epimorphism to the next factor.
**  In order to do that we define new generators for the images
**  of the generators of the finite presentation which are not definitions.
*/
void AddNewTails(presentation &Pres) {
  NrTotalGens = NrPcGens;

  /* inverse lookup tables:
     - is_dgen[i] == (exist g: Definition[g] = {DGEN,i}), so fp generator i is used to define a pc generator or an alias
     is_dpow[i] == (exist g: Definition[g] = {DPOW,i}), so ai^Exponent[i] = ag
     is_dcomm[i][j] == (exist g: Definition[g] = {DCOMM,i,j}), so [ai,aj] = ag
  */
  std::vector<bool> is_dgen(Pres.NrGens+1,false);
  std::vector<bool> is_dpow(NrPcGens+1,false);
  std::vector<std::vector<bool>> is_dcomm(NrPcGens+1);

  /* first mark aliases */
  for (unsigned i = 0; i < Pres.NrAliases; i++) {
    gen g = Pres.Aliases[i]->cont.bin.l->cont.g;
    if (is_dgen[g])
      abortprintf(3, "(At least) two definitions for generator %d", g);
    is_dgen[g] = true;
  }
    
  for (unsigned i = 1; i <= NrPcGens; i++) {
    is_dcomm[i] = std::vector<bool>(i,false);

    switch(Definition[i].t) {
    case DCOMM:
      is_dcomm[Definition[i].g][Definition[i].h] = true;
      break;
    case DGEN:
      is_dgen[Definition[i].g] = true;
      break;
    case DPOW:
      is_dpow[Definition[i].g] = true;
      break;
    }
  }

  /* first, add new pc generators for the fp generators.
     If x is an fp generator of degree d, add a pc generator in degree d,
     in the graded case, and in degree >= d, in the ungraded case.
  */
  for (unsigned i = 1; i <= Pres.NrGens; i++) {
    if (is_dgen[i] || Weight[i] > Class || (Graded && Weight[i] != Class))
      continue;
    AddSingleGenerator(Epimorphism[i], {.t = DGEN, .g = i});
    if (Debug >= 2)
      fprintf(LogFile, "# added tail a%d to epimorphic image of %s\n", NrTotalGens, Pres.GeneratorName[i]);
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
    if (pass == (TorsionExp == 0)) {
      for (unsigned i = 1; i <= NrPcGens; i++) {
	if (is_dpow[i] || !coeff_nz_p(Exponent[i]))
	  continue;
	if (Graded && (TorsionExp == 0 || Weight[i]+1 != Class))
	  continue;
	AddSingleGenerator(Power[i], {.t = DPOW, .g = i});
	if (Debug >= 2)
	  fprintf(LogFile, "# added tail a%d to non-defining torsion generator a%d\n", NrTotalGens, i);
      }
    }

    if (pass == (TorsionExp > 0)) {
      /* for all non-power pc generators g of weight <=Class-k and all
	 defining pc generators h of weight k, with g > h, and such
	 that [g,h] is not defining, add a tail to Product[g][h].

	 all other tails will be computed in Tails() out of these:
	 - if h is not defining, using Jacobi or Z-linearity;
	 - if g is a power, using Z-linearity */
      for (unsigned i = 1; i <= NrPcGens; i++) {
	if (!is_dgen[i])
	  continue;
	for (unsigned j = i+1; j <= NrPcGens; j++) {
	  if (is_dcomm[j][i])
	    continue;
	  if (Definition[j].t == DPOW)
	    continue;
	  unsigned totalweight = Weight[i]+Weight[j];
	  if (totalweight > Class || (Graded && totalweight != Class))
	    continue;
	    
	  AddSingleGenerator(Product[j][i], {.t = DCOMM, .g = j, .h = i});
	  if (Debug >= 2)
	    fprintf(LogFile, "# added tail a%d to non-defining commutator [a%d, a%d]\n", NrTotalGens, j, i);
	}
      }
    }
  }

  /*
  **  Extend the arrays of exponents, commutators etc. to the
  **  necessary size.  Let's define the newly introduced generators to
  **  be central i.e.  All of their product relations will be trivial
  **  and also they have coefficients 0.
  */

  Exponent = (coeff *) realloc(Exponent, (NrTotalGens + 1) * sizeof(coeff));
  if (Exponent == NULL)
    abortprintf(2, "AddNewTails: realloc(Exponent) failed");
  for (unsigned i = NrPcGens + 1; i <= NrTotalGens; i++)
    coeff_init_set_si(Exponent[i], TorsionExp);

  Annihilator = (coeff *) realloc(Annihilator, (NrTotalGens + 1) * sizeof(coeff));
  if (Annihilator == NULL)
    abortprintf(2, "AddNewTails: realloc(Annihilator) failed");
  for (unsigned i = NrPcGens + 1; i <= NrTotalGens; i++)
    coeff_init_set_si(Annihilator[i], 0);

  Power = (gpvec *) realloc(Power, (NrTotalGens + 1) * sizeof(gpvec));
  if (Power == NULL)
    abortprintf(2, "AddNewTails: realloc(Power) failed");
  for (unsigned i = NrPcGens + 1; i <= NrTotalGens; i++)
    Power[i] = NULL;

  Weight = (unsigned *) realloc(Weight, (NrTotalGens + 1) * sizeof(unsigned));
  if (Weight == NULL)
    abortprintf(2, "ExtendPcPres: realloc(Weight) failed");

  for (unsigned i = NrPcGens + 1; i <= NrTotalGens; i++)
    Weight[i] = Class;

  /* The Product array is not extended yet, because anyways it won't be used.
     we'll extend it later, in ReducePcPres */
    
  TimeStamp("AddNewTails()");
}

/* evaluate all relations, and add them to the relation matrix */
void EvalAllRel(presentation &Pres) {
  gpvec v = FreshVec();

  for (unsigned i = 0; i < Pres.NrAliases; i++) {
    gpvec temp = FreshVec();
    EvalRel(temp, Pres.Aliases[i]->cont.bin.r);
    Collect(v, temp);
    PopVec();
    if (Debug >= 2) {
      fprintf(LogFile, "# aliasing relation: ");
      PrintNode(LogFile, Pres.Aliases[i]);
      fprintf(LogFile, " ("); PrintVec(LogFile, v); fprintf(LogFile, ")\n");
    }
    gen g = Pres.Aliases[i]->cont.bin.l->cont.g;
    Epimorphism[g] = ResizeVec(Epimorphism[g], Length(Epimorphism[g]), Length(v));
    Copy(Epimorphism[g], v);
  }
  
  for (unsigned i = 0; i < Pres.NrRels; i++) {
    gpvec temp = FreshVec();
    EvalRel(temp, Pres.Relators[i]);
    Collect(v, temp);
    PopVec();
    if (Debug >= 2) {
      fprintf(LogFile, "# relation: ");
      PrintNode(LogFile, Pres.Relators[i]);
      fprintf(LogFile, " ("); PrintVec(LogFile, v); fprintf(LogFile, ")\n");
    }
    AddRow(v);
  }
  PopVec();
  
  TimeStamp("EvalAllRel()");
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

void EliminateTrivialGenerators(gpvec *rels, gpvec &v, int renumber[]) {
  bool copied = false;
  unsigned pos = 0;

  for (; v[pos].g != EOW;) {
    int newg = renumber[v[pos].g];
    if (newg >= 1) {
      v[pos].g = newg;
      pos++;
    } else {
      gpvec rel = rels[-newg];
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
  ShrinkCollect(v);
}

/* quotient the centre by the relations rels */
void ReducePcPres(presentation &Pres, gpvec *rels, unsigned numrels) {
  unsigned trivialgens = 0;

  if (Debug >= 2) {
    fprintf(LogFile, "# relations matrix:\n");
    for (unsigned i = 0; i < numrels; i++) {
      fprintf(LogFile, "# "); PrintVec(LogFile, rels[i]); fprintf(LogFile, "\n");
    }
  }

  /* renumber[k] = j >= 1 means generator k should be renumbered j.
     renumber[k] = j <= 0 means generator k should be eliminated using row j */
  int *renumber = new int[NrTotalGens + 1];
  
  for (unsigned k = 1, i = 0; k <= NrTotalGens; k++) {
    unsigned newk = renumber[k] = k - trivialgens;
    if (i >= numrels || k != rels[i]->g) /* no relation for k, remains */
      continue;

    if (coeff_cmp_si(rels[i]->c, 1)) { /* k is torsion, nontrivial */
      coeff_set(Exponent[newk], rels[i]->c);
      Power[newk] = NewVec(Length(rels[i]+1));
      Neg(Power[newk], rels[i]+1);
    } else { /* k is trivial, and will be eliminated */
      trivialgens++;
      renumber[k] = -i; /* mark as trivial */
    }
    i++;
  }
  unsigned newnrpcgens = NrTotalGens - trivialgens;

  /* Modify the torsions first, in decreasing order, since they're needed
     for Collect */
  for (unsigned j = NrTotalGens; j >= 1; j--)
    if (Power[j] != NULL)
      EliminateTrivialGenerators(rels, Power[j], renumber);
  
  /*  Modify the epimorphisms: */
  for (unsigned j = 1; j <= Pres.NrGens; j++)
    EliminateTrivialGenerators(rels, Epimorphism[j], renumber);
  
  /*  Modify the products: */
  for (unsigned j = 1; j <= NrPcGens; j++)
    for (unsigned l = 1; l < j; l++)
      EliminateTrivialGenerators(rels, Product[j][l], renumber);

  /* Let us alter the Definition as well. Recall that dead generator cannot
  have definition at all. It is only the right of the living ones. */
  for (unsigned i = NrPcGens + 1; i <= NrTotalGens; i++)
    if (renumber[i] >= 1)
      Definition[renumber[i]] = Definition[i];

  if (TorsionExp == 0) /* sanity check */
    for (unsigned i = 1; i <= newnrpcgens; i++)
      if (Definition[i].t == DPOW)
	abortprintf(5, "Generator %d is neither image of presentation generator nor defined as a commutator, but is a power of generator %d", i, Definition[i].g);    
  
  for (unsigned i = newnrpcgens+1; i <= NrTotalGens; i++) {
    coeff_clear(Exponent[i]);
    coeff_clear(Annihilator[i]);
  }

  delete[] renumber;
  /* we could shrink the arrays Definition, Exponent, Annihilator,
     Weight, but it's not worth it */

  /* finally extend the Product array, by trivial elements */
  Product = (gpvec **) realloc(Product, (newnrpcgens + 1) * sizeof(gpvec *));
  if (Product == NULL)
    abortprintf(2, "ReducePcPres: realloc(Product) failed");

  for (unsigned i = NrPcGens + 1; i <= newnrpcgens; i++) {
    Product[i] = (gpvec *) malloc(i * sizeof(gpvec));
    if (Product[i] == NULL)
      abortprintf(2, "ReducePcPres: realloc(Product[%d]) failed", i);

    for (unsigned j = 1; j < i; j++)
      Product[i][j] = NewVec(0);
  }
  
  TimeStamp("ReducePcPres()");

  NrPcGens = newnrpcgens;
}
