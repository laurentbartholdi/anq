# A finite presentation for an interesting  Lie ring.
 
x := AbstractGenerator( "x" );;
y := AbstractGenerator( "y" );;

L2 := rec( generators := [ x, y ],
	   relators   := [[[ y, x, x, y ]], [[ y, x, x, x, x ]],
			  [[ y, x, x, x ], [ y, x, y, y ]]]);

