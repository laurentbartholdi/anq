# lienq
A nilpotent quotient algorithm for groups and Lie algebras.

Input is a finite presentation, or more generally, a finite L-presentation, for a group or a Lie algebra.

Output is the quotient by the n-th term of an appropriate series, given by a consistent nilpotent presentation.

The possible series are:
-- lower central series gamma_{n+1} = [G,gamma_n]
-- dimension series G_{n+1} = [G,G_n]G_{n/p}^p
-- N-central series zeta_{n+1} = [G,zeta_n] zeta_{n-1}^N

The code is loosely based on Csaba Schneider's Lie nilpotent quotient code, and Wernel Nickel's NQ code.

The contents of the library is:

doc: documentations;
exs: example files;
gap: an interface to gap;
src: the C source code for lienq;
tst: lienq outputs corresponding to the files in 'exs'.
