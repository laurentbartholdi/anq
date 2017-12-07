g1 := AbstractGenerator("g1");
g2 := AbstractGenerator("g2");
a3 := AbstractGenerator("a3");
a4 := AbstractGenerator("a4");
a5 := AbstractGenerator("a5");
a9 := AbstractGenerator("a9");
a11 := AbstractGenerator("a11");
R := LiePQp( rec( 
   generators  := [ g1, g2, a3, a4, a5, a9, a11 ],
   weight      := [ 1, 1, 2, 3, 3, 4, 5 ],
   definedby   := [ -1, -2, [ 2, 1 ], [ 3, 1 ], [ 3, 2 ], [ 5, 2 ], [ 6, 2 ] 
 ],
   prime       := 5,
   dimensions  := [ 2, 1, 2, 1, 1, 0, 0, 0 ],
   productRelators := [ g2*g1/(a3), a3*g1/(a4), a3*g2/(a5), a4*g1/(a9^4), a4*a\
3/(a11), a5*g2/(a9), a9*g2/(a11) ],
   definingProducts := [ [ 2, 1 ], [ 3, 1 ], [ 3, 2 ], [ 4, 1 ], [ 4, 3 ], 
  [ 5, 2 ], [ 6, 2 ] ] ) );