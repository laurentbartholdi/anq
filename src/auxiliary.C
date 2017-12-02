/******************************************************************************
**
**               Nilpotent Quotient for Lie Algebras
** auxiliary.c                                                 Csaba Schneider
**                                                           schcs@math.klte.hu
*/

#include "lienq.h"

/****************************************************************
 to avoid malloc stress, we implement a simple stack for vector
 variables. the commands are:

 void InitStack(void) sets up the stack at begin of a large chunk of code
 void FreeStack(void) frees the stack at end of a large chunk of code
 gpvec FreshVec(void) returns a fresh vector from the top of the stack
 void PopVec(void) removes a vector from the top of the stack
 void PopVec(gpvec) pops the vector on top of the stack into its
    argument, and uses the argument as new free storage

 the vectors all have maximal capacity NrTotalGens, and are created empty.

 to be able to pop into a given position, vectors are actually allocated with
 length one greater; the returned vector starts at position 1, and position
 0 remembers the stack position in its gen field.

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

void dumpstack(const char *s) {
  return;
  fprintf(stderr,"%s:Stack is",s);
  for (unsigned i = 0; i < MaxStack; i++) fprintf(stderr," %s[%d]%p", i == NrStack ? "|| " : "", Stack[i][-1].g, Stack[i]);
  fprintf(stderr,"\n");
}

void FreeStack(void) {
  if (NrStack != 0)
    abortprintf(4, "FreeStack: stack is not empty");
  dumpstack("free");
  for (unsigned i = 0; i < MaxStack; i++)
    FreeVec(Stack[i]-1, NrTotalGens);
  free(Stack);
}

gpvec FreshVec(void) {
  if (NrStack == MaxStack) {
    MaxStack++;
    Stack = (gpvec *) realloc(Stack, MaxStack * sizeof(gpvec *));
    if (Stack == NULL)
      abortprintf(2, "FreshVec: realloc(Stack) failed");
    
    Stack[NrStack] = NewVec(NrTotalGens+1)+1;
    dumpstack("freshalloc");
    Stack[NrStack][-1].g = NrStack;
  }
  Stack[NrStack]->g = EOW;
  
  //  return Stack[NrStack++];
  NrStack++; dumpstack("fresh"); return Stack[NrStack-1];
}

void PopVec(void) {
  if (NrStack-- == 0)
    abortprintf(4, "PopVec: stack is already empty");
  
  dumpstack("pop");
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

/****************************************************************/

gpvec NewVec(unsigned size) {
  gpvec v = (gpvec) malloc ((size+1)*sizeof v[0]);
  if (v == NULL)
    abortprintf(2, "NewVec: malloc(Vector) failed");

  for (unsigned i = 0; i < size; i++)
    coeff_init(v[i].c);
  v->g = EOW;
  
  return v;
}

void FreeVec(gpvec v, unsigned size) {
  for (unsigned i = 0; i < size; i++)
    coeff_clear(v[i].c);
  free(v);
}

void FreeVec(gpvec v) {
  for (gpvec p = v; p->g != EOW; p++)
    coeff_clear(p->c);
  free(v);
}

gpvec ResizeVec(gpvec v, unsigned length) {
  v = (gpvec) realloc (v, (length+1)*sizeof v[0]);
  if (v == NULL)
    abortprintf(2, "ResizeVec: realloc(Vector) failed");

  return v;
}

/* resize a gpvec to correct length */
gpvec ResizeVec(gpvec v) {
  return ResizeVec(v, Length(v));
}
