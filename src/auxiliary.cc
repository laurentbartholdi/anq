/******************************************************************************
**
**               Nilpotent Quotient for Lie Algebras
** auxiliary.c                                                 Csaba Schneider
**                                                           schcs@math.klte.hu
*/

#include "nq.h"

/****************************************************************
 to avoid malloc stress, we implement a simple stack for vector
 variables. the commands are:

 void InitStack(void) sets up the stack at begin of a large chunk of code
 void FreeStack(void) frees the stack at end of a large chunk of code
 gpvec FreshVec(void) returns a fresh vector from the top of the stack
 void PopVec(void) removes a vector from the top of the stack

#if 0
 void PopVec(gpvec) pops the vector on top of the stack into its
    argument, and uses the argument as new free storage

 to be able to pop into a given position, vectors are actually allocated with
 length one greater; the returned vector starts at position 1, and position
 0 remembers the stack position in its gen field.
#endif
 the vectors all have maximal capacity NrTotalGens, and are created empty.

 except that vectors must be explictly popped, FreshVec() is
 essentially the same as a call to alloca.
****************************************************************/
static gpvec *Stack;
static unsigned NrStack, MaxStack;

void InitStack(void) {
  Stack = (gpvec *) malloc(0);
  NrStack = 0;
  MaxStack = 0;
}

void FreeStack(void) {
  if (NrStack != 0)
    abortprintf(4, "FreeStack: stack is not empty");
  for (unsigned i = 0; i < MaxStack; i++)
    FreeVec(Stack[i], NrTotalGens);
  free(Stack);
}

gpvec FreshVec(void) {
  if (NrStack == MaxStack) {
    MaxStack++;
    Stack = (gpvec *) realloc(Stack, MaxStack * sizeof(gpvec *));
    if (Stack == NULL)
      abortprintf(2, "FreshVec: realloc(Stack) failed");
    
    Stack[NrStack] = NewVec(NrTotalGens);
  }
  Stack[NrStack]->g = EOW;
  
  return Stack[NrStack++];
}

void PopVec(void) {
  if (NrStack-- == 0)
    abortprintf(4, "PopVec: stack is already empty");
}

#if 0
void dumpstack(const char *s) {
  return;
  fprintf(stderr,"%s:Stack is",s);
  for (unsigned i = 0; i < MaxStack; i++) fprintf(stderr," %s[%d]%p", i == NrStack ? "|| " : "", Stack[i][-1].g, Stack[i]);
  fprintf(stderr,"\n");
}

void PopVec(gpvec &p) {
  if (NrStack-- == 0)
    abortprintf(4, "PopVec: stack is already empty");

  dumpstack("beforepop");
  unsigned swapwith = p[-1].g;
  p = Stack[NrStack];
  Stack[NrStack] = Stack[swapwith];
  Stack[swapwith] = p;
  Stack[NrStack][-1].g = NrStack;
  Stack[swapwith][-1].g = swapwith;
  dumpstack("afterpop");
}
#endif

/****************************************************************/

gpvec NewVec(unsigned size) {
  gpvec v;
  v.data = (gcoeff *) malloc ((size+1)*sizeof v.data[0]);
  if (v == nullgpvec)
    abortprintf(2, "NewVec: malloc(Vector) failed");

  for (unsigned i = 0; i < size; i++) /* we don't allocate the coefficient
					 in the last position, it's only
					 used for the EOW marker */
    coeff_init(v.data[i].c);
  v->g = EOW;
  
  return v;
}

void FreeVec(gpvec v, unsigned size) {
  for (unsigned i = 0; i < size; i++)
    coeff_clear(v.data[i].c);
  free(v.data);
}

void FreeVec(gpvec v) {
  for (auto gc: v)
    coeff_clear(gc.c);
  free(v.data);
}

gpvec ResizeVec(gpvec v, unsigned oldlength, unsigned newlength) {
  if (oldlength > newlength)
    for (unsigned i = newlength; i < oldlength; i++)
      coeff_clear(v.data[i].c);

  v.data = (gcoeff *) realloc (v.data, (newlength+1)*sizeof v.data[0]);
  if (v == nullgpvec)
    abortprintf(2, "ResizeVec: realloc(Vector) failed");

  if (oldlength < newlength)
    for (unsigned i = oldlength; i < newlength; i++)
      coeff_init(v.data[i].c);

  return v;
}
