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
 sparsecvec FreshVec(void) returns a fresh vector from the top of the stack
 void PopVec(void) removes a vector from the top of the stack

#if 0
 void PopVec(sparsecvec) pops the vector on top of the stack into its
    argument, and uses the argument as new free storage

 to be able to pop into a given position, vectors are actually allocated with
 length one greater; the returned vector starts at position 1, and position
 0 remembers the stack position in its gen field.
#endif
 the vectors all have maximal capacity NrTotalGens, and are created empty.

 except that vectors must be explictly popped, FreshVec() is
 essentially the same as a call to alloca.
****************************************************************/
static sparsecvec *Stack;
static unsigned NrStack, MaxStack;

void InitStack(void) {
  Stack = (sparsecvec *) malloc(0);
  NrStack = 0;
  MaxStack = 0;
}

void FreeStack(void) {
  if (NrStack != 0)
    abortprintf(4, "FreeStack: stack is not empty");
  for (unsigned i = 0; i < MaxStack; i++)
    Stack[i].free(NrTotalGens);
  free(Stack);
}

sparsecvec FreshVec(void) {
  if (NrStack == MaxStack) {
    MaxStack++;
    Stack = (sparsecvec *) realloc(Stack, MaxStack * sizeof(sparsecvec *));
    if (Stack == NULL)
      abortprintf(2, "FreshVec: realloc(Stack) failed");
    
    Stack[NrStack].alloc(NrTotalGens);
  }
  Stack[NrStack].clear();
  
  return Stack[NrStack++];
}

void PopVec(void) {
  if (NrStack-- == 0)
    abortprintf(4, "PopVec: stack is already empty");
}
