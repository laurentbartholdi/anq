/******************************************************************************
**
**                 Nilpotent Quotient for Lie Rings
** presentation.c                                               Csaba Schneider
**                                                           schcs@math.klte.hu
*/

#include "lienq.h"
#include <time.h> // for clock

gpvec **Product,  *Power, *Epimorphism;
coeff *Exponent, *Annihilator;

deftype *Definition;

unsigned *Weight, *LastGen, Class, NrCenGens, NrPcGens, NrTotalGens;

/* add generator newgen to vector v, and store its definition */
static void AddSingleGenerator(gpvec &v, gen newgen, deftype def) {
  unsigned l;
  if (v == NULL) {
    v = NewVec(1);
    l = 0;
  } else {
    l = Length(v);
    v = ResizeVec(v, l, l + 1);
  }
  v[l].g = newgen;
  coeff_set_si(v[l].c, 1);
  v[l+1].g = EOW;
  Definition[newgen] = def;
}

static bool *DefGenerators(presentation &Pres) {
  bool *IsDefIm = new bool[Pres.NrGens + 1];

  for (unsigned i = 1; i <= Pres.NrGens; i++)
    IsDefIm[i] = false;

  /* generators admitting a definition as relator don't need a tail */
  for (unsigned i = 0; i < Pres.NrDefs; i++) {
    gen g = Pres.Definitions[i]->cont.bin.l->cont.g;
    if (IsDefIm[g])
      abortprintf(3, "(At least) two definitions for generator %d", g);
    IsDefIm[g] = true;
  }

  return IsDefIm;
}

/* initialize Pc presentation, at class 1. No products or powers are set yet. */
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
  NrPcGens = NrCenGens = 0;

  Epimorphism = (gpvec *) malloc((Pres.NrGens + 1) * sizeof(gpvec));
  if (Epimorphism == NULL)
    abortprintf(2, "InitPcPres: malloc(Epimorphism) failed");

  Definition = (deftype *) malloc((Pres.NrGens + 1) * sizeof(deftype));
  if (Definition == NULL)
    abortprintf(2, "InitPcPres: malloc(Definition) failed");

  bool *IsDefIm = DefGenerators(Pres);
  for (unsigned i = 1; i <= Pres.NrGens; i++)
    if (!IsDefIm[i]) {
      NrCenGens++;
      Epimorphism[i] = NULL;
      AddSingleGenerator(Epimorphism[i], NrCenGens, {.g = NrCenGens, .h = 0});
    }
  delete[] IsDefIm;

  NrTotalGens = NrCenGens;

  LastGen = (unsigned *) malloc(1 * sizeof(unsigned));
  if (LastGen == NULL)
    abortprintf(2, "InitPcPres: malloc(LastGen) failed");
  LastGen[0] = 0;

  /* LastGen[c] is the last generator of weight c */
  Weight = (unsigned *) malloc(1 * sizeof(unsigned));
  if (Weight == NULL)
    abortprintf(2, "InitPcPres: malloc(Weight) failed");

  /* we initialize the exponents and annihilators of our pc generators */
  Exponent = (coeff *) malloc((NrTotalGens + 1) * sizeof(coeff));
  if (Exponent == NULL)
    abortprintf(2, "InitPcPres: malloc(Exponent) failed");

  for (unsigned i = 1; i <= NrTotalGens; i++)
    coeff_init_set_si(Exponent[i], TorsionExp);
  
  Annihilator = (coeff *) malloc((NrTotalGens + 1) * sizeof(coeff));
  if (Exponent == NULL)
    abortprintf(2, "InitPcPres: malloc(Annihilator) failed");

  for (unsigned i = 1; i <= NrTotalGens; i++)
    coeff_init_set_si(Annihilator[i], 0);

  /* we reserve some space for the powers and commutators of generators,
     as well as the definitions of generators in terms of powers or
     commutators of previous ones.

     The actual values will be filled in later. */
  Power = (gpvec *) malloc((NrTotalGens + 1) * sizeof(gpvec));
  if (Power == NULL)
    abortprintf(2, "InitPcPres: malloc(Power) failed");
  for (unsigned i = 1; i <= NrTotalGens; i++)
    Power[i] = NULL;

  Product = (gpvec **) malloc((NrTotalGens + 1) * sizeof(gpvec *));
  if (Product == NULL)
    abortprintf(2, "InitPcPres: malloc(Product) failed");

  /* Finally we set the epimorphism images from the defining relations */
  InitStack();
  for (unsigned i = 0; i < Pres.NrDefs; i++) {
    gen g = Pres.Definitions[i]->cont.bin.l->cont.g;
    gpvec v = FreshVec();
    EvalRel(v, Pres.Definitions[i]->cont.bin.r);
    Epimorphism[g] = NewVec(Length(v));
    Copy(Epimorphism[g], v);
    PopVec();
    ShrinkCollect(Epimorphism[g]);
  }
  FreeStack();
}

void FreePcPres(presentation &Pres) {
  for (unsigned i = 1; i <= NrTotalGens; i++) {
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
  free(LastGen);
  free(Weight);
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

/* evaluate all relations, and add them to the relation matrix */
void EvalAllRel(presentation &Pres) {
  gpvec v = FreshVec();

  for (unsigned i = 0; i < Pres.NrDefs; i++) {
    gpvec temp = FreshVec();
    EvalRel(temp, Pres.Definitions[i]->cont.bin.r);
    Collect(v, temp);
    PopVec();
    if (Debug >= 2) {
      fprintf(OutputFile, "# defining relation: ");
      PrintNode(Pres.Definitions[i]);
      fprintf(OutputFile, " ("); PrintVec(v); fprintf(OutputFile, ")\n");
    }
    gen g = Pres.Definitions[i]->cont.bin.l->cont.g;
    Epimorphism[g] = ResizeVec(Epimorphism[g], Length(Epimorphism[g]), Length(v));
    Copy(Epimorphism[g], v);
  }
  
  for (unsigned i = 0; i < Pres.NrRels; i++) {
    gpvec temp = FreshVec();
    EvalRel(temp, Pres.Relators[i]);
    Collect(v, temp);
    PopVec();
    if (Debug >= 2) {
      fprintf(OutputFile, "# relation: ");
      PrintNode(Pres.Relators[i]);
      fprintf(OutputFile, " ("); PrintVec(v); fprintf(OutputFile, ")\n");
    }
    AddRow(v);
  }
  PopVec();
  
  TimeStamp("EvalAllRel()");
}

/* quotient the centre by the relations rels */
unsigned ReducedPcPres(presentation &Pres, gpvec *rels, unsigned numrels) {
  unsigned trivialgens = 0;

  if (Debug >= 2) {
    fprintf(OutputFile, "# relations matrix:\n");
    for (unsigned i = 0; i < numrels; i++) {
      fprintf(OutputFile, "# "); PrintVec(rels[i]); fprintf(OutputFile, "\n");
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
    for (unsigned i = 1; i <= NrTotalGens-trivialgens; i++)
      if (ispowergen(i))
	abortprintf(5, "Generator %d is neither image of presentation generator nor defined as a commutator, but is a power of generator %d", i, -Definition[i].g);    
  
  delete[] renumber;

  for (unsigned i = 0; i < trivialgens; i++)
    coeff_clear(Exponent[NrTotalGens - i]);
  
  TimeStamp("ReducedPcPres()");

  return trivialgens;
}

static void ExtendPower(void) {
  /*
  **  Extend the arrays of the generators to the necessary size.
  **  Let's define the newly introduced generators to be central i.e.
  **  All of their product relations will be trivial and also they
  **  have coefficients 0.
  */

  Exponent = (coeff *) realloc(Exponent, (NrTotalGens + 1) * sizeof(coeff));
  if (Exponent == NULL)
    abortprintf(2, "ExtendPower: realloc(Exponent) failed");

  for (unsigned i = NrPcGens + 1; i <= NrTotalGens; i++)
    coeff_init_set_si(Exponent[i], TorsionExp);

  Annihilator = (coeff *) realloc(Annihilator, (NrTotalGens + 1) * sizeof(coeff));
  if (Annihilator == NULL)
    abortprintf(2, "ExtendPower: realloc(Annihilator) failed");

  for (unsigned i = NrPcGens + 1; i <= NrTotalGens; i++)
    coeff_init_set_si(Annihilator[i], 0);

  Power = (gpvec *) realloc(Power, (NrTotalGens + 1) * sizeof(gpvec));
  if (Power == NULL)
    abortprintf(2, "ExtendPower: realloc(Power) failed");
  for (unsigned i = NrPcGens + 1; i <= NrTotalGens; i++)
    Power[i] = NULL;

  /* The Product arrays will be modified later. */
}

/*
**  The first step is to extend the epimorphism to the next factor.
**  In order to do that we define new generators for the images
**  of the generators of the finite presentation which are not definitions.
*/
void AddGen(presentation &Pres) {
  /*
  **  We want to know in advance the number of the newly introduced generators.
  **  And also don't hesitate to refer this number as 'NrCenGens'.
  */
  NrCenGens = Pres.NrGens - Pres.NrDefs + (LastGen[1] * (LastGen[1] - 1)) / 2 +
    LastGen[1] * (NrPcGens - LastGen[1]) - NrPcGens;

  bool *IsDefPower = new bool[NrPcGens + 1];
  for (unsigned i = 1; i <= NrPcGens; i++)
    IsDefPower[i] = false;

  for (unsigned i = 1; i <= NrPcGens; i++)
    if (coeff_nz_p(Exponent[i])) {
      if (ispowergen(i)) { /* a generator is defined as power */
	IsDefPower[-Definition[i].g] = true;
	NrCenGens -= LastGen[1]; /* we save that many commutators */
      } else
	NrCenGens++; /* we will add a tail */
    }

  /*
  **  In this step we sign the epimorphic images which are definitions.
  **  This is necessary because we need only to modify the images which
  **  don't define generators.
  */
  bool *IsDefIm = DefGenerators(Pres);
  
  for (unsigned i = 1; i <= NrPcGens; i++)
    if (!iscommgen(i)) {
      if (isimggen(i)) /* a generator is defined as image of
					presentation generator */
	IsDefIm[Definition[i].g] = true;
      else
	NrCenGens++;
    }

  NrTotalGens += NrCenGens;
    
  /*
  **  We have to sign the defining product relators as well in order to
  **  not get them wrong introducing new generators.
  **  IsDefRel[i][j] means that ak = [ai,aj] is the definition of ak.
  */
  bool **IsDefRel = new bool *[NrPcGens + 1];
  for (unsigned i = 1; i <= NrPcGens; i++) {
    IsDefRel[i] = new bool[LastGen[1] + 1];
    for (unsigned j = 1; j <= LastGen[1]; j++)
      IsDefRel[i][j] = false;

    if (Definition[i].h != (gen) 0 && Definition[i].h <= LastGen[1])
      IsDefRel[Definition[i].g][Definition[i].h] = true;
  }

  /* Allocate space for the Definition. */
  Definition = (deftype *) realloc(Definition, (NrTotalGens + 1) * sizeof(deftype));
  if (Definition == NULL)
    abortprintf(2, "AddGen: realloc(Definition) failed");
  
  unsigned shift = NrPcGens; /* points to the place of the new/pseudo generator. */

  /* Let's modify the epimorphic images. */
  for (unsigned i = 1; i <= Pres.NrGens; i++)
    if (!IsDefIm[i]) {
      AddSingleGenerator(Epimorphism[i], ++shift, {.g = i, .h = 0});
      if (Debug >= 2)
	fprintf(OutputFile, "# added tail a%d to epimorphic image of %s\n", shift, Pres.GeneratorName[i]);
    }

  /* now this is tricky. In mode "TorsionExp > 0", we use as basis
     generators of the form N*[ai,aj,...] with ai,aj,... of degree 1.
     In mode "TorsionExp == 0", we force N=0.

     This means that in mode "TorsionExp > 0" we favour powers, so we
     put them last; while in mode "TorsionExp == 0" we avoid them, so
     we put them first. */

  for (int flag = 0; flag < 2; flag++)
    if ((flag == 0) == (TorsionExp == 0)) {
      /* Could you guess what to do now? Right! Modify the power relations. */
      for (unsigned i = 1; i <= NrPcGens; i++)
	if (!IsDefPower[i] && coeff_nz_p(Exponent[i])) {
	  AddSingleGenerator(Power[i], ++shift, {.g = -i, .h = 0});
	  if (Debug >= 2)
	    fprintf(OutputFile, "# added tail a%d to non-defining torsion generator a%d\n", shift, i);
	}
    } else {
  /* Don't wait more to do our main task: modify the commutator relations!
   * we only add them for [ai,aj] with aj of degree 1, and ai not a power
   * generator; Product[i][j] will be set in Tails() for the other ones
   */
      for (unsigned i = 1; i <= NrPcGens; i++)
	for (unsigned j = 1; j < i && j <= LastGen[1]; j++)
	  if (!IsDefRel[i][j] && !ispowergen(i)) { /* don't add tails to [ai,aj] if ai := N*ak, since this will be N*[ak,aj] */
	    AddSingleGenerator(Product[i][j], ++shift, {.g = i, .h = j});
	    if (Debug >= 2)
	      fprintf(OutputFile, "# added tail a%d to non-defining commutator [a%d, a%d]\n", shift, i, j);
	  }
    }

  if (shift != NrTotalGens)
    abortprintf(5, "AddGen: shift (=%d) != NrTotalGens (=%d)", shift, NrTotalGens);
  
  for (unsigned i = 1; i <= NrPcGens; i++)
    delete[] IsDefRel[i];
  delete[] IsDefRel;
  delete[] IsDefIm;
  delete[] IsDefPower;
  
  ExtendPower();
  
  TimeStamp("AddGen()");
}

void GradedAddGen(void) {
  /*
  **  We want to know in advance the number of the newly introduced generators.
  **  And also don't hazitate to refer this number as 'NrCenGens'.
  */
  if (Class == 2)
    NrCenGens = (LastGen[1] * (LastGen[1] - 1)) / 2;
  else
    NrCenGens = (LastGen[Class-1]-LastGen[Class-2]) * LastGen[1];

  NrTotalGens += NrCenGens;
  
  /* Allocate space for the Definition. */
  Definition = (deftype *) realloc(Definition, (NrTotalGens + 1) * sizeof(deftype));
  if (Definition == NULL)
    abortprintf(2, "GradedAddGen: realloc(Definition) failed");
  
  unsigned shift = NrPcGens; /* points to the place of the new/pseudo generator. */

  for (unsigned i = LastGen[Class-2] + 1; i <= NrPcGens; i++)
    for (unsigned j = 1; j < i && j <= LastGen[1]; j++) {
      AddSingleGenerator(Product[i][j], ++shift, {.g = i, .h = j});
      if (Debug >= 2)
	fprintf(OutputFile, "# added tail a%d to non-defining commutator [a%d, a%d]\n", shift, i, j);
    }
  if (shift != NrTotalGens)
    abortprintf(5, "GradedAddGen: shift (=%d) != NrTotalGens (=%d)", shift, NrTotalGens);

  ExtendPower();

  TimeStamp("GradedAddGen()");
}

void ExtendPcPres(void) {
  LastGen = (unsigned *) realloc(LastGen, (Class + 1) * sizeof(unsigned));
  if (LastGen == NULL)
    abortprintf(2, "ExtendPcPres: realloc(LastGen) failed");

  LastGen[Class] = NrTotalGens;

  Weight = (unsigned *) realloc(Weight, (NrTotalGens + 1) * sizeof(unsigned));
  if (Weight == NULL)
    abortprintf(2, "ExtendPcPres: realloc(Weight) failed");

  for (unsigned i = NrPcGens + 1; i <= NrTotalGens; i++)
    Weight[i] = Class;

  /*
   * Because of the anti-symmetry we need only to store the
   * product-relations of the form [ i, j ] when i>j. Hence the form
   * of their 'matrix' turns into triangle-shaped. The row
   * corresponding to the i-th generotor will be of length i-1.
  */

  Product = (gpvec **) realloc(Product, (NrTotalGens + 1) * sizeof(gpvec *));
  if (Product == NULL)
    abortprintf(2, "ExtendPcPres: realloc(Product) failed");

  for (unsigned i = NrPcGens + 1; i <= NrTotalGens; i++) {
    Product[i] = (gpvec *) malloc(i * sizeof(gpvec));
    if (Product[i] == NULL)
      abortprintf(2, "ExtendPcPres: realloc(Product[%d]) failed", i);

    for (unsigned j = 1; j < i; j++) {
      Product[i][j] = NewVec(0);
      Product[i][j][0].g = EOW;
    }
  }

  NrPcGens += NrCenGens;
  NrCenGens = 0;
}
