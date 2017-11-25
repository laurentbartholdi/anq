# A finite presentation for an interesting  Lie ring.
 
x := AbstractGenerator( "x" );;
y := AbstractGenerator( "y" );;

L1 := rec( generators := [ x, y ],
	   relators   := [[[ y, x, y ]], [[ y, x, x, x, x, x ]]] );
