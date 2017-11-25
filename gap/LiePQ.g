LiePQpOps := rec ();

#The following function was copied from the p-qoutient program and
#modified at certain points
LiePQpOps.Print := function ( LiePQpRec )
    local  i, j, com, lst;
    Print( "LiePQp( rec( \n" );
    Print( "   generators  := ", LiePQpRec.generators, ",\n" );
    Print( "   weight      := ", LiePQpRec.weight, ",\n" );
    Print( "   definedby   := ", LiePQpRec.definedby, ",\n" );
    Print( "   prime       := ", LiePQpRec.prime, ",\n" );
    Print( "   dimensions  := ", LiePQpRec.dimensions, ",\n" );
   # Print( "   newlevel    := ", LiePQpRec.newlevel, ",\n" );
    #    Print( "   epimorphism := ", LiePQpRec.epimorphism, ",\n" );
    #    Print( "   powerRelators := [ " );
    #    for i  in [ 1 .. Length( LiePQpRec.generators ) ]  do
    #        if PowerPcp( LiePQpRec.pcp, i ) = IdWord  then
    #            Print( LiePQpRec.generators[i], "^", LiePQpRec.prime );
    #        else
    #            Print( LiePQpRec.generators[i], "^", LiePQpRec.prime, "/(", PowerPcp( LiePQpRec.pcp, i ), 
    #             ")" );
    #        fi;
    #        if i < Length( LiePQpRec.generators )  then
    #            Print( ", " );
    #        else
    #            Print( " ],\n" );
    #        fi;
    #    od;
    com := false;
    lst := [  ];
    Print( "   productRelators := [ " );
    for i  in [ 2 .. Length( LiePQpRec.generators ) ]  do
        for j  in [ 1 .. i - 1 ]  do
            if CommPcp( LiePQpRec.pcp, i, j ) <> IdWord  then
                if com  then
                    Print( ", " );
                else
                    com := true;
                fi;
                #                exponents := ExponentsPcp( P.pcp, CommPcp( P.pcp, i, j
                #                                     ) );
                Print(  LiePQpRec.generators[i], "*", LiePQpRec.generators[j], "/(",
                        CommPcp( LiePQpRec.pcp, i, j ), ")" );
                #                    List( [1..Length( P.generators )],
                #                         l->ConcatenationString( exponents[ l ],
                #                                '*', 
                Add( lst, [ i, j ] );
            fi;
        od;
    od;
    Print( " ],\n   definingProducts := ", lst, " ) )" );
end;



SaveLiePQp := SavePQp;

LiePQp := function ( G )
    local  P, i, j, cw, ii, r, rr, k, w;
    P := Pcp( "a", Length( G.generators ), G.prime, "combinatorial" );
    P := rec(
        generators := GeneratorsPcp( P ),
        pcp := P,
        prime := G.prime,
        one := Z( G.prime ) ^ 0,
        nrgens := Length( G.generators ),
        maxgennr := Length( G.generators ) + 1,
        nrnewgens := Length( G.generators ),
        defining := [ ],
        definedby := Copy( G.definedby ),
        isdefinition := [ BlistList( [  ], [  ] ) ],
        dimensions := Copy( G.dimensions ),
        #newlevel := G.newlevel,
        weight := Copy( G.weight ),    
        #epimorphism := Copy( G.epimorphism ),
        isLiePQp := true,
        operations := LiePQpOps );
    #for i  in [ 1 .. Length( G.generators ) ]  do
    #    Add( P.isdefinition[2], false );
    #od;
    for i  in [ 1 .. Length( P.generators ) * P.dimensions[1] ]  do
        Add( P.isdefinition, false );
    od;
    for k  in [ 1 .. Length( P.definedby ) ]  do
        if IsList( P.definedby[k] )  then
            j := P.definedby[k][1];
            i := P.definedby[k][2];
            P.isdefinition[1][(j - 2) * P.dimensions[1] + i] := true;
            AddSet( P.defining, TriangleIndex( j, i ) );
       # elif P.definedby[k] > 0  then
       #     P.isdefinition[P.definedby[k]] := true;
       #     AddSet( P.defining, P.definedby[k] );
        fi;
    od;
    P.identity := P.generators[1] ^ 0;
    r := PrimitiveRootMod( P.prime );
    rr := r;
    i := 1 / r mod P.prime;
    ii := i;
    P.pInverse := [ 1 ];
    while rr <> 1  do
        P.pInverse[rr] := ii;
        rr := rr * r mod P.prime;
        ii := ii * i mod P.prime;
    od;
    cw := G.weight;
    #for i  in [ 1 .. Length( G.dimensions ) ]  do
    #    for j  in [ 1 .. G.dimensions[i] ]  do
    #        cw[Length( cw ) + 1] := i;
    #    od;
    #od;
    DefineCentralWeightsPcp( P.pcp, cw );
    #for i  in [ 1 .. Length( G.generators ) ]  do
    #    w := G.powerRelators[i] ^ (-1 * 1) * G.generators[i] ^ G.prime;
    #    DefinePowerPcp( P.pcp, i, MappedWord( w, G.generators, P.generators ) 
    #     );
    #od;
    for i  in [ 1 .. Length( G.productRelators ) ]  do
        w := G.productRelators[i] ^ (-1 * 1) 
          * G.generators[G.definingProducts[i][1]] * 
             G.generators[G.definingProducts[i][2]] ;
        DefineCommPcp( P.pcp, G.definingProducts[i][1], 
         G.definingProducts[i][2], 
         MappedWord( w, G.generators, P.generators ) );
    od;
#    for i  in [ 1 .. Length( P.epimorphism ) ]  do
#        if not IsInt( P.epimorphism[i] )  then
#            P.epimorphism[i] := MappedWord( G.epimorphism[i], G.generators, 
#               P.generators );
#        fi;
#    od;
    return P;
end;


#This function removes an element from a list.
RemoveList := function ( list, k )
    return List( Union( [ 1 .. k - 1 ], [ k + 1 .. Length( list ) ] ), 
                 function ( l )
        return list[l];
    end );
end;


LieInitPQp := function ( d, p )
    local record;
    record := InitPQp( d, p );
    Unbind( record.isPQp );
    record.defining := Copy( record.defining[ 1 ] );
    record.isdefinition := Copy( record.isdefinition[ 1 ] );
    record.isLiePQp := true;
    record.dimensions[1] := d;
    record.newlevel := [ 1, d + 1 ];
    record.operations := Copy( LiePQpOps );
    record.weight := List( [1..d], l->1);
    return record;
end;

# We introduce the new lie generators of weight c corrisponding the 
# product-relators ab = 0 where a is of weight c-1 and b is of weight 1.
IntroduceGeneratorsLiePQp := function ( P )
    local class, nrweight1, nrweightmax, i, j, newgenlist, newcommutatorlist,
          genlist, helplist, isdefinition;

    class := P.weight[ Length( P.weight ) ] + 1;
    #As the first step we count how many new generators we must
    #introduce and also introduce them whith their centralweights.
    nrweight1 := P.dimensions[ 1 ];
    nrweightmax := P.dimensions[ Length( P.dimensions ) ];
    P.nrgens := Length( GeneratorsPcp( P.pcp ) );
    newgenlist := [ ];
    newcommutatorlist := [ ];
    for i in [1..nrweight1] do
        for j in [P.newlevel[ Length( P.newlevel ) - 1]..P.nrgens] do
#           Error();
            if j>i then
                Add( newgenlist, ConcatenationString( "a",
                        String( Length( newgenlist ) + P.maxgennr ) ) );
                Add( newcommutatorlist, [ j, i ] );
                Add( P.definedby, [ j, i ] );
                Add( P.defining, [ j, i ] );
                P.isdefinition[ ( j - 2 ) * nrweight1 + i ] := true;
            else
                if ( j - 2 ) * nrweight1 + i > 0 then
                    P.isdefinition[ ( j - 2 ) * nrweight1 + i ] := false;
                fi;     
            fi;
        od;
    od;
    ExtendCentralPcp( P.pcp, newgenlist, P.prime );
    genlist := GeneratorsPcp( P.pcp );
    Append( P.weight, List( [1..Length( newgenlist )], l->class ) );
    DefineCentralWeightsPcp( P.pcp, P.weight );
    for i in newcommutatorlist do
        DefineCommPcp( P.pcp, i[ 1 ], i[ 2 ], genlist[
                Position( newcommutatorlist, [i[ 1 ], i[ 2 ]] ) + P.nrgens ] );
    od;
    P.generators := GeneratorsPcp( P.pcp );
    Add( P.dimensions, Length( newgenlist ) );
    P.maxgennr := P.maxgennr + Length( newgenlist );
    P.nrgens := Length( P.generators );
    P.nrnewgens := Length( newgenlist );
    Add( P.newlevel, P.newlevel[ Length( P.newlevel ) ] + P.nrnewgens );
    #    helplist := [ ];
    #    isdefinition := P.isdefinition;
    #    for i in [1..Length( P.isdefinition )] do
    #        if Position( isdefinition, true ) = 1 then 
    #            Add( helplist, i );
    #        fi;
    #        isdefinition := List( [2..Length( isdefinition )],
    #                                l->isdefinition[ l ]);
    #    od;
    #    Error( );
    for i in [1..Length( P.isdefinition )] do
         if P.isdefinition[ i ] <> true  then 
            P.isdefinition[ i ] := false;
        fi;
    od;   
    for i in [Length( P.isdefinition ) + 1..
            ( nrweightmax - 2 ) * nrweight1 + nrweight1] do
        P.isdefinition[ i ] := false;
    od;         
    return( P );
end;

#Now we are  modifying the other relations of weight c. We have to
#modify those relations ba = 0 where b is of wheight less then c - 1,
#and a is of weight greater then 1 using the Jacobi identity.
#The idea can be found in the paper of Havas et al.
ModifyOtherRelationsLiePQp := function ( P , class )
    local weighta, a, weightb, b, exponents, word, defa;
    for weighta in [2..class - 1] do
        weightb := class - weighta;
        for a in [ P.newlevel[ weighta ]..P.newlevel[ weighta + 1 ] -
                1 ] do
            for b in [ P.newlevel[ weightb ]..P.newlevel[ weightb + 1 ] -
                    1 ] do
                if b > a then 
                    #compute the value of the product ba
                    #a = defa[ 1 ] * defa[ 2 ] ( = cd )
                     #Print(a,b); 
                    defa := P.definedby[ a ];
#Error();

                    exponents := ExponentsPcp(P.pcp, CommPcp( P.pcp, CommPcp(
                                         P.pcp, defa[ 2 ], b ), defa[ 1 ] ) )
                                 - ExponentsPcp( P.pcp, CommPcp( P.pcp,
                                         CommPcp( P.pcp, defa[ 1 ], b ),
                                         defa[ 2 ] ) );
                    #ba = b(cd) = -cdb = dbc + bcd = bcd - bdc
                    word := NormalWordPcp( P.pcp, Product( [1..Length( 
                                    P.generators )], 
                                    l -> P.generators[ l ]^exponents[
                                            l ] ) ) ;
                    DefineCommPcp( P.pcp, b, a, word );
                fi;
            od;
        od;
    od;
end;

#The next function checks the consistency relations in the lie ring P,
#and returns the matrix of the linear equations that hold for the
#generators of P.
#The basic idea is due to Havas et al. 
ConsistencyLiePQp := function ( P, class )
    local a, b, c, weightb, weightc, initc, termc, linsys, coeff;
    #a is of weight 1.
    linsys := [ ];
    for a in [1..P.dimensions[ 1 ]] do
        for weightb in [1..class - 2] do
            #w( a ) + w( b ) + w( c ) = class
            weightc := class - weightb - 1;
            for b in [Maximum( a + 1, P.newlevel[ weightb ]
                    )..P.newlevel[ weightb + 1] - 1] do
                for c in [Maximum( b + 1,
                        P.newlevel[ weightc ] )..P.newlevel[ weightc +
                                1 ] - 1] do
                    #compute the coefficients of 'abc + bca + cab'
                    coeff := Sum( [1..Length( P.generators )], l->
                                  ExponentsPcp( P.pcp, CommPcp(
                                          P.pcp, a, b )
                                          )[ l ] * ExponentsPcp(
                                                  P.pcp, CommPcp(
                                                          P.pcp, l, c
                                                          ) ) )  +
                             Sum( [1..Length( P.generators )], l->
                                  ExponentsPcp( P.pcp, CommPcp( P.pcp,
                                          b, c ) )[ l ] * ExponentsPcp(
                                                  P.pcp, CommPcp(
                                                          P.pcp, l, a
                                                          ) ) ) +
                             Sum( [1..Length( P.generators )],
                                  l->ExponentsPcp( P.pcp, CommPcp(
                                          P.pcp, c, a ) )[ l ] *
                                  ExponentsPcp( P.pcp, CommPcp( P.pcp,
                                          l, b ) ) );
                    coeff := List( [1..Length( coeff )], l->coeff[ l ]
                                   mod P.prime );
                    #                    Print(a, b, c, "\n");
                    if coeff <> List( coeff , l -> 0 ) 
                       then
                        Add( linsys, coeff );
                        #                        Print( a, b, c );
                    fi;
                od;
            od;
        od;
    od;
    return( linsys );
end;

#The following function almost the same as the TriangulizeMat but 
#works in the prime field of p elements.
TrianguleMat := function ( mat, pinverse )
    local  m, n, i, j, k, row, zero, prime;
    prime := Length( pinverse ) + 1;
    #    InfoMatrix1( "#I  TrianguleMat called\n" );
    if mat <> [  ]  then
        m := Length( mat );
        n := Length( mat[1] );
        zero := 0 * mat[1][1];
        #        InfoMatrix2( "#I    nonzero columns: \c" );
        i := 0;
        for k  in [ 1 .. n ]  do
            j := i + 1;
            while j <= m and mat[j][k] mod prime= zero  do
                j := j + 1;
            od;
            if j <= m  then
                #               InfoMatrix2( k, " \c" );
                i := i + 1;
                row := mat[j];
                mat[j] := mat[i];
                #the next line was modified
                mat[i] := pinverse[ row[k] mod prime ] * row;
                for j  in [ 1 .. m ]  do
                    if i <> j and mat[j][k] mod prime <> zero  then
                        mat[j] := mat[j] - mat[j][k] * mat[i];
                    fi;
                od;
            fi;
        od;
        mat := List( [1..m], l -> List( [1..n], l1 -> mat[ l ][ l1 ] mod
                       prime )  );
    fi;
    #    InfoMatrix2( "\n" );
    #    InfoMatrix1( "#I  TrianguleMat returns\n" );
    return( mat );
end;



#This function solves any linear equation
#given with its coefficient matrix. It returns a list containg as its
#ith entry [ [ i_1, k_1 ], [i_2, k_2] ... [ i_n, k_n ] ] meaning that
#x_i = k_1 * x_i_1 + ... + k_n * x_i_n where x_1 ... x_n are the generators
#for the lie ring
SolveLinSysLiePQp := function( linsys, pinverse )
    local newi, row, nonzero, nonzeropos, i, j, m, list, k, result,
          prime;
    if linsys <> [ ] then
        prime := Length( pinverse ) + 1;
        linsys := TrianguleMat( linsys, pinverse );
        #pinverse := [ 1, 3, 2, 4 ];
        # rank := RankMat( linsys );
        result := List( [1..Length( linsys[ 1 ] ) ], l->[ [ l, 1 ] ] ); 
        for i in Reversed([1..Length( linsys )]) do
            row := linsys[ i ];
            if row <> List( row, l -> 0 ) then
                #we look up the first non-zero element in row
                nonzeropos := 0;
                repeat
                    nonzeropos := nonzeropos + 1;
                until row[ nonzeropos ] <> 0;
                nonzero := Copy( row[ nonzeropos ] );
                list := [ ];
                    for k in [ nonzeropos + 1..Length( row ) ] do
                        if row[ k ] <> 0 then
                            Add( list, [ k, -row[ k ]/pinverse[
                                    nonzero mod prime ] ] );
                        fi;
                    od;
                    result[nonzeropos]:= list;
            fi;
        od;
    else
        result := [ ];
    fi;
    return( result );
end;




#The next function drops out the generators that couse the inconsistency of
#the lie ring using the output of the function SolveLinSysLiePQp.
DropGeneratorsLiePQp := function( P, list )
    local i, j, word, shrinklist;
    shrinklist :=[ ];
    for i in [1..Length( list )] do
        if list[ i ] = [ ] or list[ i ][ 1 ][ 1 ] <> i then
            word := IdWord;
            for j in list[ i ] do
                word := word * P.generators[ j[ 1 ] ]^j[ 2 ];
            od;
            #if i = 17 then 
             #   Error();
            #fi;
            
            DefineCommPcp( P.pcp, P.definedby[ i ][ 1 ], P.definedby[
                    i ][ 2 ], NormalWordPcp( P.pcp, word ) );
            Add( shrinklist, [ i, P.definedby[ i ] ] );
            #ShrinkPcp( P.pcp, [ i ] );
            #P.generators := GeneratorsPcp( P.pcp );
            P.dimensions[ Length( P.dimensions ) ] := 
              P.dimensions[ Length( P.dimensions) ] - 1;
            P.weight := RemoveList( P.weight, Length( P.weight ) );
            P.nrgens := P.nrgens - 1;
            P.nrnewgens := P.nrnewgens - 1;
            P.newlevel[ Length( P.newlevel ) ] := 
              P.newlevel[ Length( P.newlevel ) ] - 1;
            P.isdefinition[ ( P.definedby[ i ][ 1 ] - 2 ) *
                    P.dimensions[ 1 ] + P.definedby[ i ][ 2 ] ] := false;
            P.defining := RemoveList( P.defining, Position(
                                  P.defining, [ P.definedby[ i ][ 1 ],
                                          P.definedby[ i ][ 2 ] ] ) );
            #P.definedby := RemoveList( P.definedby, i);
        fi;
    od;
    if shrinklist <> [ ] then 
        ShrinkPcp( P.pcp, List( [1..Length( shrinklist )],
                l->shrinklist[l][1] ) );
        P.generators := GeneratorsPcp( P.pcp );
        for i in shrinklist do
            P.definedby := RemoveList( P.definedby, Position(
                                   P.definedby, i[ 2 ] ) );
        od;
    fi;
    return( P );
end;


#This function creates a consistent product presentation of the
#factor-ring of the free lie ring with <nrgens> genetators and of
#characteristic prime, with respect to the class-th term of the lower
#central series of G.
LibLiePQp := function( nrgens, prime, class )
    local P, i;
    PrintTo("lie.info","The first level:\n");
    P:=LieInitPQp( nrgens, prime );
    AppendTo("lie.info",P,"\n\n\n");
    for i in [2..class] do
        AppendTo("lie.info","The ",i,"th level:\n");
        P := IntroduceGeneratorsLiePQp( P );
       AppendTo("lie.info",P,"\n\n\nAfter modifying the non defining",
                " relations:\n");
        ModifyOtherRelationsLiePQp( P, i );
        AppendTo("lie.info",P,"\n\n\nThe consistency relations for the ",
                i,"th level:\n ");
        AppendTo("lie.info",ConsistencyLiePQp(P,i),"\n\n\n");
        AppendTo("lie.info","\n\n\nThe solution of the linear equation ",
               "system:\n",SolveLinSysLiePQp(ConsistencyLiePQp(P,i),P.pInverse));
        AppendTo("lie.info","\n\n\nLet's drop the extra generators:\n");
        DropGeneratorsLiePQp( P, SolveLinSysLiePQp( ConsistencyLiePQp(
                P, i ), P.pInverse ) );
        AppendTo("lie.info",P,"\n\n\nModify those certain relations again:\n");
        
        ModifyOtherRelationsLiePQp( P, i );
       AppendTo("lie.info",P,"\n\n\n");
    od;
    return P;
end;


#The following function enforces the defining relations of the Lie-ring.
#The method is the same as the method was for the inconsistency problem.
#It returns the matrix of the linear equation system which holds for
#the maximum weight-generators of the lie ring. 
EnforceRelatorsLiePQp := function( P, R )
    local map, i, j, k, word, linsys, bigword, wtonegens, exponents;
    linsys := [ ];
    wtonegens := List( [1..P.dimensions[ 1 ]], l -> P.generators[
                         l ] );
    map := x -> MappedWord( x, R.generators, wtonegens );

    for i in R.relators do
        if Length( i[ 1 ] ) = P.weight[ Length( P.weight ) ] then
            bigword := IdWord;
            for k in i do
                word := map( k[ 1 ] );
                for j in List( [2..Length(k)], l -> k[ l ] ) do
                    word := CommPcp( P.pcp, word, map( j ) );
                od;
                bigword := ProductPcp( P.pcp, bigword, word ); 
            od;
            exponents := ExponentsPcp( P.pcp, bigword );
            if exponents <> List( exponents, l -> 0 ) then
                Add( linsys, exponents );       
            fi;
        fi;
    od;
    return( linsys );
end;


#This function creates the consistent product presentation for the Lie-ring
#<G>/<G_class> where G_class is the class-th term of the lower central series
#of G. G is given by as a record with two entries, generators and relators.
LiePQuotient := function( G, prime, class )
    local P, i, linsys, solution, nrgens;
    nrgens := Length( G.generators );
    #PrintTo("lie.info","The first level:\n");
    P:=LieInitPQp( nrgens, prime );
    #AppendTo("lie.info",P,"\n\n\n");
    for i in [2..class] do
     #   AppendTo("lie.info","The ",i,"th level:\n");
        P := IntroduceGeneratorsLiePQp( P );
     #   AppendTo("lie.info",P,"\n\n\nAfter modifying the non defining",
      #          " relations:\n");
        ModifyOtherRelationsLiePQp( P, i );
     #   AppendTo("lie.info",P,"\n\n\nThe consistency relations for the ",
     #           i,"th level:\n ");
     #   AppendTo("lie.info",ConsistencyLiePQp(P,i),"\n\n\n");
     #   AppendTo("lie.info","\n\n\nThe solution of the linear equation ",
     #          "system:\n",SolveLinSysLiePQp(ConsistencyLiePQp(P,i),P.pInverse));
      #  AppendTo("lie.info","\n\n\nLet's drop the extra generators:\n");
        linsys := ConsistencyLiePQp(P,i);
        if linsys <> [ ] then
            solution := SolveLinSysLiePQp( linsys, P.pInverse );
            DropGeneratorsLiePQp( P, solution );
            ModifyOtherRelationsLiePQp( P, i );
        fi;
      #  AppendTo("lie.info",P,"\n\n\nModify those certain relations again:\n");
        
      #  AppendTo("lie.info",P,"\n\n\n");
        linsys := EnforceRelatorsLiePQp( P, G );
        if linsys <> [ ] then
            solution := SolveLinSysLiePQp( linsys, P.pInverse );
            DropGeneratorsLiePQp( P, solution );
            ModifyOtherRelationsLiePQp( P, i );
        fi;
      #  AppendTo("lie.info","Enforce the defining relations:\n",P,"\n\n\n");
        SaveLiePQp("ex3.g",P,"R");
    od;
    return P;
end;







 
