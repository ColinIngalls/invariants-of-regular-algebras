


LoadPackage( "qpa" );

####################################################################################################################################################


nthGradeOfFreeAlgebraIdeal:= function( kQ, I, n ) #Takes an ideal I of the free algebra kQ and an integer n, return the
                                                  #nth grade I_n of I
  local rels, L, i, MonomialsOfLesserDegree, V, iter, nGens, 3tuple, prod ;
  rels:= GeneratorsOfIdeal( I );
	if n = 0 then
		V:= Subspace( kQ, [ One( kQ ) ], "basis" );
	else
		V:= Subspace( kQ, NthPowerOfArrowIdeal( kQ, n ), "basis" );
	fi;
	L:= [ [ One( kQ ) ] ];
	nGens:= [ ];
	for i in [1..n] do
		Add( L, NthPowerOfArrowIdeal( kQ, i ) );
	od;
	MonomialsOfLesserDegree:= Union( L );
	iter:= IteratorOfCartesianProduct( MonomialsOfLesserDegree, rels, MonomialsOfLesserDegree );
	for 3tuple in iter do
    prod:= Product( 3tuple );
		if prod in V then								#checks if the product is homogeneous of degree n
			Add( nGens, prod );
		else
			continue ;
		fi;
	od;
	return Subspace( kQ, nGens ) ;
end;



nProductSpace:= function( Subs... )     #Takes a set
  local TList, L, V, kQ, GensCart, Gens, x, ProdSpace ;
  TList:= [];
  for V in Subs do
    Add( TList, Parent( V ) = Parent( Subs[1] ) );
  od;
  if ForAll( TList, IsTrue ) = false then
    Error( "Make sure the inputted subsets have the same parents");
  else
    kQ:= Parent( Subs[1] );
    L:= [];
    for V in Subs do
      Add( L, Basis( V ) );
    od;
    GensCart:= IteratorOfCartesianProduct( L );
    Gens:= [];
    for x in GensCart do
      Add( Gens, Product( x ) );
    od;
    ProdSpace:= Subspace( kQ, Gens );
    return ProdSpace ;
  fi;
end;



nthKoszulComplexObjectByRels:= function( A, rels, p ) #Inputs a quadratic algebra GradedA and
                                          #outputs the space W_p = (A!_p)* as a
                                          #subspace of k<X>, the free algebra of
                                          #which A is a quotient
  local x1, x2, kQ, R, Degrees, MaxDeg, L, i, j, kQi, kQj, Wp ;
#  A:= GradedA[1]; ListA:= GradedA[2];
  kQ:= OriginalPathAlgebra( A );
  R:= Subspace( kQ, rels );
  if p > 2 or p = 2 then
    MaxDeg:= p - 2;
    L:= [];
    for i in [0..MaxDeg] do
      j:= p - 2 - i ;
      kQi:= nthGradeOfAlgebra( kQ, i ); kQj:= nthGradeOfAlgebra( kQ, j );
      Add( L, nProductSpace( kQi, R, kQj ) );
    od;
    Wp:= Intersection( L );
  elif p = 1 or p = 0 then
    Wp:= nthGradeOfAlgebra( kQ, p );
  elif p = -1 then
    Wp:= Subspace( kQ, [ Zero( kQ ) ] );
#    Wp:= TrivialSubspace( A );
  else
    Error( "Enter a nonnegative integer" );
  fi;
  return Wp ;
end;



nthKoszulComplexObjectByRels2:= function( A, rels, p ) #Inputs a quadratic algebra GradedA and
                                          #outputs the space W_p = (A!_p)* as a
                                          #subspace of k<X>, the free algebra of
                                          #which A is a quotient
  local x1, x2, kQ, R, Degrees, MaxDeg, L, i, j, kQi, kQj, Wp ;
#  A:= GradedA[1]; ListA:= GradedA[2];
  kQ:= OriginalPathAlgebra( A );
  R:= Subspace( kQ, rels );
  if p > 2 or p = 2 then
    MaxDeg:= p - 2;
    L:= [];
    for i in [0..MaxDeg] do
      j:= p - 2 - i ;
      kQi:= nthGradeOfAlgebra( kQ, i ); kQj:= nthGradeOfAlgebra( kQ, j );
      Add( L, nProductSpace( kQi, R, kQj ) );
    od;
    Wp:= Intersection( L );
  elif p = 1 or p = 0 then
    Wp:= nthGradeOfAlgebra( kQ, p );
  elif p = -1 then
    Wp:= Subspace( kQ, [ Zero( kQ ) ] );
#    Wp:= TrivialSubspace( A );
  else
    Error( "Enter a nonnegative integer" );
  fi;
  return Wp ;
end;



GradednthKoszulComplexObjectByRels:= function( A, rels, p )
  local Wp ;
  Wp:= nthKoszulComplexObjectByRels( A, rels, p ) ;
  return [ Wp, [ [ Wp, p ] ] ];
end;



GradedHomKoszulComplexObjectByRels:= function( GradedA, rels, p )
  local A, Wp, K, GradedWp, GradedHomWp, HomWp ;
  if p > -1 then
    A:= GradedA[1]; Wp:= nthKoszulComplexObjectByRels( A, rels, p );
    GradedWp:= [ Wp, [ [Wp, p ] ] ] ;
    K:= LeftActingDomain( A );
    GradedHomWp:= HOMGrading( K, GradedWp, GradedA );
  else
    HomWp:= TrivialSubspace( GradedHomKoszulComplexObjectByRels( GradedA, rels, 1 )[1] );
    GradedHomWp:= GradedSubset( GradedHomKoszulComplexObjectByRels( GradedA, rels, 1 ), HomWp );
  fi;
  return GradedHomWp ;
end;

####################################################################################################################################################

#These next functions will serve to define the differential of the Koszul complex of an algebra A

LeftmostProductDecomposition:= function( kQ, x )  #This inputs a homogeneous element x of degree n
                                                  #of a free algebra kQ and outputs, as a list, its
                                                  #"leftmost decomposition" y_k, where x = \sum_k x_k y_k
                                                  # for y_k is sum of monomials of degree n-1
  local xfam, rep, gensums, gens, yklist, i, j, fakeyk, yk;
  xfam:= FamilyObj( x ); rep:= ExtRepOfObj( x ); gensums:= rep[2];
  gens:= GeneratorsOfAlgebra( kQ );
  yklist:= [ ];
  for i in [1..Length(gens)] do
    fakeyk:= [0, [] ];
    for j in [1..Length(gensums)] do
      if IsList( gensums[j] ) = true and gensums[j][1] = i then
        if Length( gensums[j] ) = 1 then
          Add( fakeyk[2], [ 1 ] ); Add( fakeyk[2], gensums[j+1] );
        else
          Add( fakeyk[2], gensums[j]{[2..Length(gensums[j])]} ); Add( fakeyk[2], gensums[j+1] );
        fi;
      fi;
    od;
    yk:= ObjByExtRep( xfam, fakeyk );
    Add( yklist, yk );
  od;
  return yklist ;
end;



RightmostProductDecomposition:= function( kQ, x ) #This inputs a homogeneous element x of degree n
                                             #of a free algebra kQ and outputs, as a list, its
                                             #"factored decomposition" \sum_k y_k x_k, where
                                             #y_k is a sum of monomials of degree n-1
  local xfam, rep, gensums, gens, yklist, i, j, fakeyk, yk;
  xfam:= FamilyObj( x ); rep:= ExtRepOfObj( x ); gensums:= rep[2];
  gens:= GeneratorsOfAlgebra( kQ );
  yklist:= [ ];
  for i in [1..Length(gens)] do
    fakeyk:= [0, [] ];
    for j in [1..Length(gensums)] do
      if IsList( gensums[j] ) = true and gensums[j][Length( gensums[j] )] = i then
        if Length( gensums[j] ) = 1 then
          Add( fakeyk[2], [ 1 ] ); Add( fakeyk[2], gensums[j+1] );
        else
          Add( fakeyk[2], gensums[j]{[1..( Length(gensums[j]) - 1 )]} ); Add( fakeyk[2], gensums[j+1] );
        fi;
      fi;
    od;
    yk:= ObjByExtRep( xfam, fakeyk );
    Add( yklist, yk );
  od;
  return yklist ;
end;

####################################################################################################################################################


#HomKoszulDifferentialImage:= function( f, Wp, p )  #inputs a linear map f: Wp0 = W_{p-1} -> A and
                                                #outputs the linear map Dpf: W_p -> A defined in
                                                #the paper Koszul Calculus, after using the
                                                #isomorphism Hom_{A^e}(A(x)Wp(x)A, A) = Hom_k(Wp, A)
#  local Dpf, kQ, Wp0, A,Agens, bWp, DpfImageList, x, xLeftDecomp, xRightDecomp, i, L ;
#  kQ:= Parent( Wp ); bWp:= Basis( Wp );
#  Wp0:= Source( f ); A:= Range( f );
#  Agens:= GeneratorsOfAlgebra( A ); Agens:= DuplicateRemover( Agens );
#  DpfImageList:= [];
#  for x in bWp do
#    xLeftDecomp:= LeftmostProductDecomposition( kQ, x );
#    xRightDecomp:= RightmostProductDecomposition( kQ, x );
#    for i in [1..Length( Agens )] do
#      L:= [];
#      Add( L, Agens[i]*Image( f, xLeftDecomp[i] ) + (-1)^p * Image( f, xRightDecomp[i] )*Agens[i] );
#    od;
#    Add( DpfImageList, Sum( L ) );
#  od;
#  Dpf:= LeftModuleHomomorphismByImages( Wp, A, bWp, DpfImageList );
#  return Dpf ;
#end;


HomKoszulDifferentialImage:= function( f, Wp, p )  #inputs a linear map f: Wp0 = W_{p-1} -> A and
                                                #outputs the linear map Dpf: W_p ->, A defined in
                                                #the paper Koszul Calculus, after using the
                                                #isomorphism Hom_{A^e}(A(x)Wp(x)A, A) = Hom_k(Wp, A)
  local Dpf, kQ, Wp0, A,Agens, bWp, DpfImageList, x, xLeftDecomp, xRightDecomp, Summand, i, L ;
  kQ:= Parent( Wp ); bWp:= Basis( Wp );
  Wp0:= Source( f ); A:= Range( f );
  Agens:= GeneratorsOfAlgebra( A ); Agens:= DuplicateRemover( Agens );
  DpfImageList:= [];
  for x in bWp do
    xLeftDecomp:= LeftmostProductDecomposition( kQ, x );
    xRightDecomp:= RightmostProductDecomposition( kQ, x );
    L:= [];
    for i in [1..Length( Agens )] do
      Summand:= Agens[i]*Image( f, xLeftDecomp[i] ) - (-1)^(p-1) * Image( f, xRightDecomp[i] )*Agens[i] ;
#      Summand:= Image( f, xRightDecomp[i] )*Agens[i] - (-1)^(p-1) * Agens[i]*Image( f, xLeftDecomp[i] ) ;
      Add( L, Summand );
    od;
    Add( DpfImageList, Sum( L ) );
  od;
  Dpf:= LeftModuleHomomorphismByImages( Wp, A, bWp, DpfImageList );
  return Dpf ;
end;



StandaloneHomKoszulDifferential:= function( A, rels, p ) #outputs Dp: Hom( Wp0, A) -> Hom( Wp, A )
  local Dp, K, Wp0, HomWp0, Wp, HomWp, BasisHomWp0, f, ImageList ;
  K:= LeftActingDomain( A );
  Wp0:= nthKoszulComplexObjectByRels( A, rels, p-1 ); HomWp0:= Hom( K, Wp0, A );
  Wp:= nthKoszulComplexObjectByRels( A, rels, p ); HomWp:= Hom( K, Wp, A );
  BasisHomWp0:= Basis( HomWp0 ); ImageList:= [];
  for f in BasisHomWp0 do
    Add( ImageList, HomKoszulDifferentialImage( f, Wp, p ) );
  od;
  Dp:= LeftModuleHomomorphismByImages( HomWp0, HomWp, BasisHomWp0, ImageList );
  return Dp ;
end;



HomKoszulDifferential:= function( A, Wp, HomWp0, HomWp, p ) #outputs Dp: Hom( Wp0, A) -> Hom( Wp, A )
  local Dp, K, Wp0, BasisHomWp0, f, ImageList ;
  K:= LeftActingDomain( A );
#  Wp0:= nthKoszulComplexObject( A, p-1 ); HomWp0:= Hom( K, Wp0, A );
#  Wp:= nthKoszulComplexObject( A, p ); HomWp:= Hom( K, Wp, A );
  BasisHomWp0:= Basis( HomWp0 ); ImageList:= [];
  for f in BasisHomWp0 do
    Add( ImageList, HomKoszulDifferentialImage( f, Wp, p ) );
  od;
  Dp:= LeftModuleHomomorphismByImages( HomWp0, HomWp, BasisHomWp0, ImageList );
  return Dp ;
end;


#GradedKoszulCohomologyMapsByRels:= function( kQ, rels, p, i )
#  local A, GradedA, Wp, Wp1, GradedHomWp0, GradedHomWp, GradedHomWp1, HomWp0i, HomWpi, HomWp1i,
#        Dpi, Dp1i ;
#  A:= GBQuotient( kQ, rels ); GradedA:= GradingOfAlgebra( A );
#  Wp:= nthKoszulComplexObjectByRels( A, rels, p );
#  Wp1:= nthKoszulComplexObjectByRels( A, rels, p + 1 );
#  GradedHomWp0:= GradedHomKoszulComplexObjectByRels( GradedA, rels, p-1 ) ;
#  GradedHomWp:= GradedHomKoszulComplexObjectByRels( GradedA, rels, p ) ;
#  GradedHomWp1:= GradedHomKoszulComplexObjectByRels( GradedA, rels, p + 1 ) ;
#  if i = "full" then
#    HomWp0i:= GradedHomWp0[1] ;
#    HomWpi:= GradedHomWp[1] ;
#    HomWp1i:= GradedHomWp1[1] ;
#  elif IsInt( i ) = true then
#    HomWp0i:= GradedPositionFinder( GradedHomWp0, i );
#    HomWpi:= GradedPositionFinder( GradedHomWp, i );
#    HomWp1i:= GradedPositionFinder( GradedHomWp1, i );
#  fi;
#  Dpi:= HomKoszulDifferential( A, Wp, HomWp0i, HomWpi, p );
#  Dp1i:= HomKoszulDifferential( A, Wp1, HomWpi, HomWp1i, p + 1 );
#  return [ Dp1i, Dpi ];
#end;



####################################################################################################################################################

#Below is an attempt to make functions that can compute the Koszul cohomology (in degree n)
#of quadratic algebras of possibly infinite dimension


HomSpaceBasis2:= function( GradedA, B, Ai, Bj)  #Returns a basis for the subspace Hom(Ai, Bj) of Hom(A, B), without explicitly computing the subspace
	local x1, i, A, bA, bAi, bBj, cart, L, f, HomBase ;
	A:= GradedA[1];
#	bA:= BasisForGradedAlgebra( GradedA );
 	bA:= Basis( A );
	bAi:= Basis( Ai );																					#We have as an assumption that Basis( Ai ) is a subset of Basis( A )
	bBj:= Basis( Bj );
	cart:= Cartesian( bAi, bBj );
	HomBase:= [ ];
	for x1 in cart do
		i:= Position( bA, x1[1] );
		L:= [];
		CopyListEntries( [ Zero( B ) ], 1, 0, L, 1, 1, Length( Basis( A ) ) );    #This is to define the map sending the basis element x1[1] to x1[2], and all
		L[i]:= x1[2];																															#other basis elements to 0
		f:= LeftModuleHomomorphismByImages( A, B, bA, L );
		Add( HomBase, f );
	od;
	return HomBase;
end;



nthGradedHom2:= function( K, GradedA, B, n )   #This function outputs the nth graded Hom set Hom( A, B )_n of linear maps A -> B of degree n
	local i, x1, f, A, ListA, ListB, BaseHomAB, nListB, RestrictedSubspaceGens, HomSubspace, SummandList;
	A:= GradedA[1]; ListA:= GradedA[2];
	nListB:= [ ];
	for x1 in ListA do
		Add( nListB, nthGradeOfAlgebra( B, n + x1[2] ) ) ;
	od;
	SummandList:= [ ];
	for i in [1..Length( ListA )] do
    if Dimension( ListA[i][1] ) = 0 and Dimension( nListB[i] ) = 0 then
      f:= LeftModuleHomomorphismByImages( ListA[i][1], nListB[i], Basis( ListA[i][1] ), Basis( nListB[i] ) );
      HomSubspace:= VectorSpace( K, [ f ] );
    else
#  		RestrictedSubspaceGens:= HomSpaceBasis2( GradedA, B, ListA[i][1], nListB[i] );
  		HomSubspace:= Hom( K, ListA[i][1], nListB[i] ); #GAP is incapable of computing the Hom between two trivial spaces
#  		HomSubspace:= VectorSpace( K, RestrictedSubspaceGens );
    fi;
		Add( SummandList, HomSubspace );
	od;
	return Sum( SummandList );
end;



HomKoszulDifferentialImage2:= function( f, Wp, A, p, i )  #inputs a linear map f: Wp0 = W_{p-1} -> A_{i+p-1} and
                                                          #outputs the linear map Dpf: W_p -> A_{i+p} defined in
                                                          #the paper Koszul Calculus, after using the
                                                          #isomorphism Hom_{A^e}(A(x)Wp(x)A, A) = Hom_k(Wp, A)
  local Dpf, kQ, Wp0, Agens, bWp, DpfImageList, one, x, xLeftDecomp, xRightDecomp, Summand, j, L ;
  kQ:= Parent( Wp );
#  bWp:= GeneratorsOfLeftModule( Wp );
  bWp:= Basis( Wp );
  Wp0:= Source( f ); #A:= Range( f );
  Agens:= GeneratorsOfAlgebra( A ); Agens:= DuplicateRemover( Agens );
  DpfImageList:= [];
  one:= One( A );
  for x in bWp do
    xLeftDecomp:= LeftmostProductDecomposition( kQ, x );
    xRightDecomp:= RightmostProductDecomposition( kQ, x );
    L:= [];
    for j in [1..Length( Agens )] do
      Summand:= Agens[j]*Image( f, xLeftDecomp[j] ) - (-1)^(p-1) * Image( f, xRightDecomp[j] )*Agens[j] ;
#      Summand:= Image( f, xRightDecomp[j] )*Agens[j] - (-1)^(p-1) *Agens[j]*Image( f, xLeftDecomp[j] ) ;
      Add( L, Summand );
    od;
    Add( DpfImageList, Sum( L ) );
  od;
  if i = "full" then
    Dpf:= LeftModuleHomomorphismByImages( Wp, A, bWp, DpfImageList );
#  elif IsInt( i ) = true and i > -1 then
  elif IsInt( i ) = true then
    Dpf:= LeftModuleHomomorphismByImages( Wp, nthGradeOfAlgebra( A, p + i ), bWp, DpfImageList );
                                          #p + i because Hom( A, B)_n = \otimes_i Hom( A_i, B_[n+i])
                                          #and because of the trvial grading of W_p.
  fi;
  return Dpf ;
end;



HomKoszulDifferential2:= function( A, Wp, HomWp0i, HomWpi, p, i ) #outputs Dp: Hom( Wp0, A) -> Hom( Wp, A )
  local Dp, K, Wp0, BasisHomWp0i, f, ImageList ;
  K:= LeftActingDomain( A );
#  Wp0:= nthKoszulComplexObject( A, p-1 ); HomWp0:= Hom( K, Wp0, A );
#  Wp:= nthKoszulComplexObject( A, p ); HomWp:= Hom( K, Wp, A );
  BasisHomWp0i:= GeneratorsOfLeftModule( HomWp0i );
#  BasisHomWp0i:= Basis( HomWp0i );
  ImageList:= [];
  for f in BasisHomWp0i do
    Add( ImageList, HomKoszulDifferentialImage2( f, Wp, A, p, i ) );
  od;
  Dp:= LeftModuleHomomorphismByImages( HomWp0i, HomWpi, BasisHomWp0i, ImageList );  #This is, currently, unending when A
                                                                                      #infinite-dimensional.
  return Dp ;
end;



GradedKoszulCohomologyMapsByRels:= function( A, kQ, rels, p, i )
  local K, GradedA, GradedWp0, GradedWp, GradedWp1, Wp0, Wp, Wp1, HomWp0i, HomWpi, HomWp1i,
        Ai, Dpi, Dp1i ;
  K:= LeftActingDomain( kQ );
#  A:= GBQuotient( kQ, rels );
  GradedWp0:= GradednthKoszulComplexObjectByRels( A, rels, p - 1 ); Wp0:= GradedWp0[1];  #Print( "Wp0 \n" );
  GradedWp:= GradednthKoszulComplexObjectByRels( A, rels, p ); Wp:= GradedWp[1];  #Print( "Wp \n" );
  GradedWp1:= GradednthKoszulComplexObjectByRels( A, rels, p + 1 ); Wp1:= GradedWp1[1]; #Print( "Wp1 \n" );
  if p < 0 then
    Error( "Please enter a nonnegative homological degree" );
  elif IsFiniteDimensional( A ) = false and i = "full" then
    Error( "Cannot compute the full cohomology of an infinite-dimensional algebra (yet)");
  elif i = "full" then
    GradedA:= GradingOfAlgebra( A );
    HomWp0i:= Hom( K, Wp0, A );
    HomWpi:= Hom( K, Wp, A );
    HomWp1i:= Hom( K, Wp1, A );
  elif IsInt( i ) = true then
    HomWp0i:= Hom( K, Wp0, nthGradeOfAlgebra( A, i + p-1 ) ) ;
    HomWpi:= Hom( K, Wp, nthGradeOfAlgebra( A, i + p ) ) ;  #This works because of the trivial grading of Wp, for all p
    HomWp1i:= Hom( K, Wp1, nthGradeOfAlgebra( A, i+p+1 ) );
  else
    Error( "Please enter valid inputs" );
  fi;
  if Dimension( HomWp0i ) = 0 then
    Print("Dim( Hom( W_{", p-1, "}, A)_", i, "= 0 \n");
  fi;
  if Dimension( HomWpi ) = 0 then
    Print("Dim( Hom( W_{", p, "}, A)_", i, "= 0 \n");
  fi;
  if Dimension( HomWp1i ) = 0 then
    Print("Dim( Hom( W_{", p+1, "}, A)_", i, "= 0 \n");
  fi;
  if Dimension( HomWp0i ) = 0 or Dimension( HomWpi ) = 0 then
    Dpi:= ZeroMapping( HomWp0i, HomWpi ); Print("D^{p}_i = 0 \n");
  else
    Dpi:= HomKoszulDifferential2( A, Wp, HomWp0i, HomWpi, p, i );
  fi;
  if Dimension( HomWpi ) = 0 or Dimension( HomWp1i ) = 0 then
    Dp1i:= ZeroMapping( HomWpi, HomWp1i ); Print("D^{p+1}_i = 0 \n");
  else
    Dp1i:= HomKoszulDifferential2( A, Wp1, HomWpi, HomWp1i, p+1, i );
  fi;
  return [ Dp1i, Dpi, A ];
end;




####################################################################################################################################################

#The following will serve to define the differentials \tilde{b_K} in the paper Koszul Calculus

TildeHomKoszulDifferentialImage:= function( GradedA, f, Wp, p ) #inputs a linear map f: Wp0 = W_{p-1} -> A and
                                                                #outputs the linear map Dpf: W_p ->, A defined in
                                                                #the paper Koszul Calculus, after using the
                                                                #isomorphism Hom_{A^e}(A(x)Wp(x)A, A) = Hom_k(Wp, A)
  local Dpf, kQ, Wp0, A, ListA, IndexA, Amin, Amax, j, m, Agens, bWp, DpfImageList, x1, x2, xLeftDecomp, xRightDecomp, Summand, i, L ;
  A:= GradedA[1]; ListA:= GradedA[2]; IndexA:= [];
  for x1 in ListA do
    Add( IndexA, x1[2] );
  od;
  Amin:= Minimum( IndexA ); Amax:= Maximum( IndexA );
  for j in [Amin..Amax] do
    if IsSubset( GradedPositionFinder( GradedA, j ), Image( f ) ) = true then
      m:= j ;
    fi;
  od;
  kQ:= Parent( Wp ); bWp:= Basis( Wp );
  Wp0:= Source( f ); #A:= Range( f );
  Agens:= GeneratorsOfAlgebra( A ); Agens:= DuplicateRemover( Agens );
  DpfImageList:= [];
  for x2 in bWp do
    xLeftDecomp:= LeftmostProductDecomposition( kQ, x2 );
    xRightDecomp:= RightmostProductDecomposition( kQ, x2 );
    L:= [];
    for i in [1..Length( Agens )] do
      Summand:= Agens[i]*Image( f, xLeftDecomp[i] ) - (-1)^(m) * Image( f, xRightDecomp[i] )*Agens[i] ;
      Add( L, Summand );
    od;
    Add( DpfImageList, Sum( L ) );
  od;
  Dpf:= LeftModuleHomomorphismByImages( Wp, A, bWp, DpfImageList );
  return Dpf ;
end;



TildeHomKoszulDifferential:= function( GradedA, Wp, GradedHomWp0, GradedHomWp, p ) #outputs Dp: Hom( Wp0, A) -> Hom( Wp, A )
  local Dp, A, K, Wp0, BasisHomWp0, f, ImageList ;
  A:= GradedA[1]; K:= LeftActingDomain( A );
#  Wp0:= nthKoszulComplexObject( A, p-1 ); HomWp0:= Hom( K, Wp0, A );
#  Wp:= nthKoszulComplexObject( A, p ); HomWp:= Hom( K, Wp, A );
#  BasisHomWp0:= BasisForGradedAlgebra( GradedHomWp0 );
  BasisHomWp0:= Basis( GradedHomWp0[1] );
  ImageList:= [];
  for f in BasisHomWp0 do
    Add( ImageList, TildeHomKoszulDifferentialImage( GradedA, f, Wp, p ) );
  od;
  Dp:= LeftModuleHomomorphismByImages( GradedHomWp0[1], GradedHomWp[1], BasisHomWp0, ImageList );
  return Dp ;
end;



TildeGradedKoszulCohomologyMapsByRels:= function( kQ, rels, p, i )
  local A, GradedA, Wp, Wp1, GradedHomWp0, GradedHomWp, GradedHomWp1, HomWp0i, HomWpi, HomWp1i,
        Dpi, Dp1i ;
  A:= GBQuotient( kQ, rels ); GradedA:= GradingOfAlgebra( A );
  Wp:= nthKoszulComplexObjectByRels( A, rels, p );
  Wp1:= nthKoszulComplexObjectByRels( A, rels, p + 1 );
  GradedHomWp0:= GradedHomKoszulComplexObjectByRels( GradedA, rels, p-1 ) ;
  GradedHomWp:= GradedHomKoszulComplexObjectByRels( GradedA, rels, p ) ;
  GradedHomWp1:= GradedHomKoszulComplexObjectByRels( GradedA, rels, p + 1 ) ;
  if i = "full" then
    HomWp0i:= GradedHomWp0 ;
    HomWpi:= GradedHomWp ;
    HomWp1i:= GradedHomWp1 ;
  elif IsInt( i ) = true then
    HomWp0i:= [ GradedPositionFinder( GradedHomWp0, i ), [ [ GradedPositionFinder( GradedHomWp0, i ), 0 ] ] ];
    HomWpi:= [ GradedPositionFinder( GradedHomWp, i ), [ [ GradedPositionFinder( GradedHomWp, i ), 0 ] ] ];
    HomWp1i:= [ GradedPositionFinder( GradedHomWp1, i ), [ [ GradedPositionFinder( GradedHomWp1, i ), 0 ] ] ];
  fi;
  Dpi:= TildeHomKoszulDifferential( GradedA, Wp, HomWp0i, HomWpi, p );
  Dp1i:= TildeHomKoszulDifferential( GradedA, Wp1, HomWpi, HomWp1i, p + 1 );
  return [ Dp1i, Dpi, A ];
end;



GradedKoszulCohomologyMapsByRelsViaTilde:= function( kQ, rels, p, i ) #This functions uses the isomorphism HH^i(A)_j = ~HH^{i+j}(A!)_-i to
                                                                      #compute the Koszul cohomology of a given quadratic algebra.
  local V, maps ;
  V:= QuadraticDualByRelsNoQuotient( kQ, rels );
  maps:= TildeGradedKoszulCohomologyMapsByRels( V[2], V[3], p+i, -i );
  return maps ;
end;



####################################################################################################################################################
#The following is an attempt to compute the modified Hochschild cohomology of algebras which may not be finite-dimensional

TildeHomKoszulDifferentialImage2:= function( A, f, Wp, p, j ) #inputs a linear map f: Wp0 = W_{p-1} -> A and
                                                                #outputs the linear map Dpf: W_p ->, A defined in
                                                                #the paper Koszul Calculus, after using the
                                                                #isomorphism Hom_{A^e}(A(x)Wp(x)A, A) = Hom_k(Wp, A)
  local Dpf, kQ, Wp0, m, Am, Agens, bWp, DpfImageList, x1, x2, xLeftDecomp, xRightDecomp, Summand, i, L ;
  m:= p+j;
  Am:= nthGradeOfAlgebra( A, m );
  kQ:= Parent( Wp ); bWp:= Basis( Wp );
  Wp0:= Source( f ); #A:= Range( f );
  Agens:= GeneratorsOfAlgebra( A ); Agens:= DuplicateRemover( Agens );
  DpfImageList:= [];
  for x2 in bWp do
    xLeftDecomp:= LeftmostProductDecomposition( kQ, x2 );
    xRightDecomp:= RightmostProductDecomposition( kQ, x2 );
    L:= [];
    for i in [1..Length( Agens )] do
      Summand:= Agens[i]*Image( f, xLeftDecomp[i] ) - (-1)^(m) * Image( f, xRightDecomp[i] )*Agens[i] ;
      Add( L, Summand );
    od;
    Add( DpfImageList, Sum( L ) );
  od;
  Dpf:= LeftModuleHomomorphismByImages( Wp, Am, bWp, DpfImageList );
  return Dpf ;
end;



TildeHomKoszulDifferential2:= function( A, Wp, HomWp0, HomWp, p, i ) #outputs Dp: Hom( Wp0, A) -> Hom( Wp, A )
  local Dp, K, Wp0, BasisHomWp0, f, ImageList ;
  K:= LeftActingDomain( A );
#  Wp0:= nthKoszulComplexObject( A, p-1 ); HomWp0:= Hom( K, Wp0, A );
#  Wp:= nthKoszulComplexObject( A, p ); HomWp:= Hom( K, Wp, A );
  BasisHomWp0:= Basis( HomWp0 );
  ImageList:= [];
  for f in BasisHomWp0 do
    Add( ImageList, TildeHomKoszulDifferentialImage2( A, f, Wp, p, i ) );
  od;
  Dp:= LeftModuleHomomorphismByImages( HomWp0, HomWp, BasisHomWp0, ImageList );
  return Dp ;
end;



TildeGradedKoszulCohomologyMapsByRels2:= function( kQ, rels, p, i )
  local A, K, Wp0, Wp, Wp1, HomWp0, GradedHomWp, GradedHomWp1, HomWp0i, HomWpi, HomWp1i, L,
        Dpi, Dp1i ;
  K:= LeftActingDomain( kQ );
  A:= GBQuotient( kQ, rels );
  Wp0:= nthKoszulComplexObjectByRels( A, rels, p - 1 );
  Wp:= nthKoszulComplexObjectByRels( A, rels, p );
  Wp1:= nthKoszulComplexObjectByRels( A, rels, p + 1 );
  if i = "full" then
    L:= TildeGradedKoszulCohomologyMapsByRels( kQ, rels, p, i );
  elif IsInt( i ) = true then
    HomWp0i:= Hom( K, Wp0, nthGradeOfAlgebra( A, i+p-1 ) ) ;
    HomWpi:= Hom( K, Wp, nthGradeOfAlgebra( A, i+p ) ) ;  #This works because of the trivial grading of Wp, for all p
    HomWp1i:= Hom( K, Wp1, nthGradeOfAlgebra( A, i+p+1 ) );
    Dpi:= TildeHomKoszulDifferential2( A, Wp, HomWp0i, HomWpi, p, i );
    Dp1i:= TildeHomKoszulDifferential2( A, Wp1, HomWpi, HomWp1i, p + 1, i );
    L:= [ Dp1i, Dpi, A ];
  fi;
  return L;
end;



GradedKoszulCohomologyMapsByRelsViaTilde2:= function( kQ, rels, p, i ) #This functions uses the isomorphism HH^i(A)_j = ~HH^{i+j}(A!)_-i to
                                                                      #compute the Koszul cohomology of a given quadratic algebra.
  local V, maps ;
  V:= QuadraticDualByRelsNoQuotient( kQ, rels );
  maps:= TildeGradedKoszulCohomologyMapsByRels2( V[2], V[3], p+i, -i );
  return maps ;
end;

####################################################################################################################################################

#The following contains functions useful when filling out the file AlgebraCohomologyTable.xlsx

IngallsKoszulCohomologyMaps:= function( kQ, rels )
  local A, L ;
  A:= kQ/rels;
  L:= [];
  L[1]:= GradedKoszulCohomologyMapsByRels( A, kQ, rels, 0, 0);
  L[2]:= GradedKoszulCohomologyMapsByRels( A, kQ, rels, 0, 1);
  L[3]:= GradedKoszulCohomologyMapsByRels( A, kQ, rels, 0, 2);
  L[4]:= GradedKoszulCohomologyMapsByRels( A, kQ, rels, 1, -1);
  L[5]:= GradedKoszulCohomologyMapsByRels( A, kQ, rels, 1, 0);
  L[6]:= GradedKoszulCohomologyMapsByRels( A, kQ, rels, 1, 1);
  L[7]:= GradedKoszulCohomologyMapsByRels( A, kQ, rels, 2, -2);
  L[8]:= GradedKoszulCohomologyMapsByRels( A, kQ, rels, 2, 0);
  return L ;
end;



IngallsDualKoszulCohomologyMaps:= function( kQ, rels )
  local V, DualA, DualkQ, Dualrels, L ;
  V:= QuadraticDualByRels( kQ, rels );
  DualA:= V[1]; DualkQ:= V[2]; Dualrels:= V[3];
  L:= [];
  L[1]:= GradedKoszulCohomologyMapsByRels( DualA, DualkQ, Dualrels, 0, 0);
  L[2]:= GradedKoszulCohomologyMapsByRels( DualA, DualkQ, Dualrels, 0, 1);
  L[3]:= GradedKoszulCohomologyMapsByRels( DualA, DualkQ, Dualrels, 0, 2);
  L[4]:= GradedKoszulCohomologyMapsByRels( DualA, DualkQ, Dualrels, 1, -1);
  L[5]:= GradedKoszulCohomologyMapsByRels( DualA, DualkQ, Dualrels, 1, 0);
  L[6]:= GradedKoszulCohomologyMapsByRels( DualA, DualkQ, Dualrels, 1, 1);
  L[7]:= GradedKoszulCohomologyMapsByRels( DualA, DualkQ, Dualrels, 2, -2);
  L[8]:= GradedKoszulCohomologyMapsByRels( DualA, DualkQ, Dualrels, 2, 0);
  return L ;
end;



IngallsTildeKoszulCohomologyMaps:= function( kQ, rels )
  local V, DualkQ, Dualrels, L ;
  V:= QuadraticDualByRels( kQ, rels );
  DualkQ:= V[2]; Dualrels:= V[3];
  L:= [];
  L[1]:= TildeGradedKoszulCohomologyMapsByRels( DualkQ, Dualrels, 0, 0);
  L[2]:= TildeGradedKoszulCohomologyMapsByRels( DualkQ, Dualrels, 0, 1);
  L[3]:= TildeGradedKoszulCohomologyMapsByRels( DualkQ, Dualrels, 0, 2);
  L[4]:= TildeGradedKoszulCohomologyMapsByRels( DualkQ, Dualrels, 1, -1);
  L[5]:= TildeGradedKoszulCohomologyMapsByRels( DualkQ, Dualrels, 1, 0);
  L[6]:= TildeGradedKoszulCohomologyMapsByRels( DualkQ, Dualrels, 1, 1);
  L[7]:= TildeGradedKoszulCohomologyMapsByRels( DualkQ, Dualrels, 2, -2);
  L[8]:= TildeGradedKoszulCohomologyMapsByRels( DualkQ, Dualrels, 2, 0);
  return L ;
end;



IngallsKoszulCohomologyMapsViaTilde:= function( kQ, rels )
  local V, L ;
  V:= QuadraticDualByRels( kQ, rels );
  Print("Dual\n") ;
  L:= [];
  L[1]:= TildeGradedKoszulCohomologyMapsByRels( V[2], V[3], 0, 0); Print("1\n");
  L[2]:= TildeGradedKoszulCohomologyMapsByRels( V[2], V[3], 1, -1); Print("2\n");
  L[3]:= TildeGradedKoszulCohomologyMapsByRels( V[2], V[3], 2, -2); Print("3\n");
  L[4]:= TildeGradedKoszulCohomologyMapsByRels( V[2], V[3], 0, 1); Print("4\n");
  L[5]:= TildeGradedKoszulCohomologyMapsByRels( V[2], V[3], 1, 0); Print("5\n");
  L[6]:= TildeGradedKoszulCohomologyMapsByRels( V[2], V[3], 2, -1); Print("6\n");
  L[7]:= TildeGradedKoszulCohomologyMapsByRels( V[2], V[3], 0, 2); Print("7\n");
  L[8]:= TildeGradedKoszulCohomologyMapsByRels( V[2], V[3], 2, 0); Print("8\n");
  return L ;
end;



IngallsKoszulCohomologyMapsViaTildeTest:= function( kQ, rels )
  local V, L ;
  V:= QuadraticDualByRels( kQ, rels );
  Print("Dual\n") ;
  L:= [];
  L[1]:= TildeGradedKoszulCohomologyMapsByRels( V[2], V[3], 0, 0); Print("1\n");
  L[2]:= TildeGradedKoszulCohomologyMapsByRels( V[2], V[3], 1, -1); Print("2\n");
#  L[3]:= TildeGradedKoszulCohomologyMapsByRels( V[2], V[3], 2, -2); Print("3\n");
  L[4]:= TildeGradedKoszulCohomologyMapsByRels( V[2], V[3], 0, 1); Print("4\n");
  L[5]:= TildeGradedKoszulCohomologyMapsByRels( V[2], V[3], 1, 0); Print("5\n");
#  L[6]:= TildeGradedKoszulCohomologyMapsByRels( V[2], V[3], 2, -1); Print("6\n");
  L[7]:= TildeGradedKoszulCohomologyMapsByRels( V[2], V[3], 0, 2); Print("7\n");
  L[8]:= TildeGradedKoszulCohomologyMapsByRels( V[2], V[3], 2, 0); Print("8\n");
  return L ;
end;



IngallsKoszulCohomologyMapsViaTilde2:= function( kQ, rels )
  local V, L ;
  V:= QuadraticDualByRels( kQ, rels );
  Print("Dual\n") ;
  L:= [];
  L[1]:= TildeGradedKoszulCohomologyMapsByRels2( V[2], V[3], 0, 0); Print("1\n");
  L[2]:= TildeGradedKoszulCohomologyMapsByRels2( V[2], V[3], 1, -1); Print("2\n");
  L[3]:= TildeGradedKoszulCohomologyMapsByRels2( V[2], V[3], 2, -2); Print("3\n");
  L[4]:= TildeGradedKoszulCohomologyMapsByRels2( V[2], V[3], 0, 1); Print("4\n");
  L[5]:= TildeGradedKoszulCohomologyMapsByRels2( V[2], V[3], 1, 0); Print("5\n");
  L[6]:= TildeGradedKoszulCohomologyMapsByRels2( V[2], V[3], 2, -1); Print("6\n");
  L[7]:= TildeGradedKoszulCohomologyMapsByRels2( V[2], V[3], 0, 2); Print("7\n");
  L[8]:= TildeGradedKoszulCohomologyMapsByRels2( V[2], V[3], 2, 0); Print("8\n");
  return L ;
end;



MapsDim:= function( maps )
  return Dimension( Kernel( maps[1] ) ) - Dimension( Image( maps[2] ) );
end;


MapsProj:= function( maps )
  local Ker, Im, phi ;
  Ker:= Kernel( maps[1] );
  Im:= Image( maps[2] );
  phi:= NaturalHomomorphismBySubspace( Ker, Im );
  return phi ;
end;


####################################################################################################################################################

#The purpose of the following code is to find the deformations of the relations of an algebra, say A. Explicitly, we start by finding a basis for
#the kernel of the differential Hom(W_2, A) -> Hom(W_3, A)_0. Then, for each function f in the basis, we create a list of "ordered pairs" (list
#of two elements), where the first element is a basis element of Source(f) = W_2, and the second is its corresponding image under f.

DeformationOfRelationsSetup:= function( A, kQ, rels )
  local K, GradedW2, W2, GradedW3, W3, HomW2, HomW3, diff ;
  K:= LeftActingDomain( kQ );
  GradedW2:= GradednthKoszulComplexObjectByRels( A, rels, 2 ); W2:= GradedW2[1];  #Print( "Wp \n" );
  GradedW3:= GradednthKoszulComplexObjectByRels( A, rels, 3 ); W3:= GradedW3[1];
  HomW2:= Hom( K, W2, nthGradeOfAlgebra( A, 2 ) ) ;
  HomW3:= Hom( K, W3, nthGradeOfAlgebra( A, 3 ) ) ;
  diff:= HomKoszulDifferential2( A, W3, HomW2, HomW3, 3, 0 );
  return diff ;
end;



FunctionBasisImages:= function( f )
  local L, SourceBasis, b ;
#  f:= KerBasis[i];
  SourceBasis:= Basis( Source( f ) );
  L:= [];
  for b in SourceBasis do
    Add( L, [ b, Image( f, b ) ] ) ;
  od;
  return L;
end;



DeformationOfRelations:= function( diff )
  local Ker, KerBasis, L, n, i ;
  Ker:= Kernel( diff );
  KerBasis:= Basis( Ker ) ;
  L:= [ ];
  n:= Length( KerBasis );
  for i in [1..n] do
    Add(L, FunctionBasisImages( KerBasis[i] ) ) ;
  od;
  return L;
end;



DeformationOfRelationsDisplay:= function( L )
  local n, i ;
  n:= Length( L );
  for i in [1..n] do
    Print( "Basis( Kernel )[", i, "] \n");
    GoodListDisplay( L[i] );
    Print( "\n\n" );
  od;
end;
