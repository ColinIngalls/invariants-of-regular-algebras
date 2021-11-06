


LoadPackage( "qpa" );


####################################################################################################################################################

DuplicateRemover:= function( L )
  local NewL, x ;
  NewL:= [];
  for x in L do
    if not x in NewL then
      Add( NewL, x );
    fi;
  od;
  return NewL ;
end;

####################################################################################################################################################


DualSpace:= function( V )
  local k, Vast;
  k:= LeftActingDomain( V );
  Vast:= Hom( k, V, k );
  return Vast;
end;


DualOfDualIsomorphism:= function( V, Vast, Vastast ) #Takes in a vector space V, its dual Vast and double dual Vastast
                                                    #return the isomorphism ev: V -> Vastast
  local k, ev, v, f, BasisV, BasisVast, ImageList, L, evImage ;
  k:= LeftActingDomain( V );
  BasisV:= Basis( V ); BasisVast:= Basis( Vast );
  ImageList:= [ ];
  for v in BasisV do
    L:= [ ];
    for f in BasisVast do
      Add( L, Image( f, v ) );
    od;
    evImage:= LeftModuleHomomorphismByImages( Vast, k, BasisVast, L );
    Add( ImageList, evImage );
  od;
  ev:= LeftModuleHomomorphismByImages( V, Vastast, BasisV, ImageList );
  return ev;
end;


DualOfQuotientToAnnihilatorIsomorphism:= function( V, W ) #V is a vector space, W is a subspace of V
  local pi, VW, Vast, VWast, bVWast, ImageList, f, fpi, phi ;
  VW:= V/W;
  pi:= NaturalHomomorphismBySubspace( V, W );
  Vast:= DualSpace( V );
  VWast:= DualSpace( VW );
  bVWast:= Basis( VWast );
  ImageList:= [];
  for f in bVWast do
    fpi:= CompositionMapping( f, pi );
    Add( ImageList, fpi );
  od;
  phi:= LeftModuleHomomorphismByImages( VWast, Vast, bVWast, ImageList );
  return phi ;
end;


AnnihilatorOfSubspace:= function( V, W )
  local phi, AnnW ;
  phi:= DualOfQuotientToAnnihilatorIsomorphism( V, W );
  AnnW:= Image( phi );
  return AnnW ;
end;


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


nthKoszulComplexObject:= function( A, p ) #Inputs a quadratic algebra GradedA and
                                          #outputs the space W_p = (A!_p)* as a
                                          #subspace of k<X>, the free algebra of
                                          #which A is a quotient
  local x1, x2, kQ, rels, R, Degrees, MaxDeg, L, i, j, kQi, kQj, Wp ;
#  A:= GradedA[1]; ListA:= GradedA[2];
  kQ:= OriginalPathAlgebra( A ); rels:= RelationsOfAlgebra( A );
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
    Wp:= TrivialSubspace( A );
  else
    Error( "Enter a nonnegative integer" );
  fi;
  return Wp ;
end;

GradednthKoszulComplexObject:= function( A, p )
  local Wp ;
  Wp:= nthKoszulComplexObject( A, p ) ;
  return [ Wp, [ [ Wp, p ] ] ];
end;


GradedHomKoszulComplexObject:= function( GradedA, p )
  local A, Wp, K, GradedWp, GradedHomWp, HomWp ;
  if p > -1 then
    A:= GradedA[1]; Wp:= nthKoszulComplexObject( A, p );
    GradedWp:= [ Wp, [ [Wp, p ] ] ] ;
    K:= LeftActingDomain( A );
    GradedHomWp:= HOMGrading( K, GradedWp, GradedA );
  else
    HomWp:= TrivialSubspace( GradedHomKoszulComplexObject( GradedA, 1 )[1] );
    GradedHomWp:= GradedSubset( GradedHomKoszulComplexObject( GradedA, 1 ), HomWp );
  fi;
  return GradedHomWp ;
end;

####################################################################################################################################################


LinearMapLeftScalarMultiplication:= function( x, f ) #f is a linear map Alg -> A, x is in A, returns the linear function x*f(a)
  local Alg, BaseAlg, L, a, xf;
  Alg:= Source( f );
  BaseAlg:= Basis( Alg );
  L:= [];
  for a in BaseAlg do
    Add( L , x*Image( f, a ) );
  od;
  xf:= LeftModuleHomomorphismByImages( Alg, Range( f ), BaseAlg, L );
  return xf;
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
                                                #outputs the linear map Dpf: W_p -> A defined in
                                                #the paper Koszul Calculus, after using the
                                                #isomorphism Hom_{A^e}(A(x)Wp(x)A, A) = Hom_k(Wp, A)
  local Dpf, kQ, Wp0, A,Agens, bWp, DpfImageList, x, xLeftDecomp, xRightDecomp, i, L ;
  kQ:= Parent( Wp ); bWp:= Basis( Wp );
  Wp0:= Source( f ); A:= Range( f );
  Agens:= GeneratorsOfAlgebra( A ); Agens:= DuplicateRemover( Agens );
  DpfImageList:= [];
  for x in bWp do
    xLeftDecomp:= LeftmostProductDecomposition( kQ, x );
    xRightDecomp:= RightmostProductDecomposition( kQ, x );
    for i in [1..Length( Agens )] do
      L:= [];
      Add( L, Image( f, xRightDecomp[i] )*Agens[i] - (-1)^p*Agens[i]*Image( f, xLeftDecomp[i] ) );
    od;
    Add( DpfImageList, Sum( L ) );
  od;
  Dpf:= LeftModuleHomomorphismByImages( Wp, A, bWp, DpfImageList );
  return Dpf ;
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


StandaloneHomKoszulDifferential:= function( A, p ) #outputs Dp: Hom( Wp0, A) -> Hom( Wp, A )
  local Dp, K, Wp0, HomWp0, Wp, HomWp, BasisHomWp0, f, ImageList ;
  K:= LeftActingDomain( A );
  Wp0:= nthKoszulComplexObject( A, p-1 ); HomWp0:= Hom( K, Wp0, A );
  Wp:= nthKoszulComplexObject( A, p ); HomWp:= Hom( K, Wp, A );
  BasisHomWp0:= Basis( HomWp0 ); ImageList:= [];
  for f in BasisHomWp0 do
    Add( ImageList, HomKoszulDifferentialImage( f, Wp, p ) );
  od;
  Dp:= LeftModuleHomomorphismByImages( HomWp0, HomWp, BasisHomWp0, ImageList );
  return Dp ;
end;


KoszulCohomologyMaps:= function( A, p )
  local K, Wp0, Wp, Wp1, HomWp0, HomWp, HomWp1, Dp, Dp1;
#  K:= LeftActingDomain( A );
#  Wp0:= nthKoszulComplexObject( A, p-1 ); HomWp0:= Hom( K, Wp0, A );
#  Wp:= nthKoszulComplexObject( A, p-1 ); HomWp:= Hom( K, Wp, A );
#  Wp1:= nthKoszulComplexObject( A, p-1 ); HomWp1:= Hom( K, Wp1, A );
Dp:= HomKoszulDifferential( A, p ); Dp1:= HomKoszulDifferential( A, p+1 );
return [ Dp1, Dp ];
end;


GradedKoszulCohomologyMaps:= function( GradedA, p, i )
  local A, Wp, Wp1, GradedHomWp0, GradedHomWp, GradedHomWp1, HomWp0i, HomWpi, HomWp1i,
        Dpi, Dp1i ;
  A:= GradedA[1];
  Wp:= nthKoszulComplexObject( A, p );
  Wp1:= nthKoszulComplexObject( A, p + 1 );
  GradedHomWp0:= GradedHomKoszulComplexObject( GradedA, p-1 ) ;
  GradedHomWp:= GradedHomKoszulComplexObject( GradedA, p ) ;
  GradedHomWp1:= GradedHomKoszulComplexObject( GradedA, p + 1 ) ;
  if i = "full" then
    HomWp0i:= GradedHomWp0[1] ;
    HomWpi:= GradedHomWp[1] ;
    HomWp1i:= GradedHomWp1[1] ;
  elif IsInt( i ) = true then
    HomWp0i:= GradedPositionFinder( GradedHomWp0, i );
    HomWpi:= GradedPositionFinder( GradedHomWp, i );
    HomWp1i:= GradedPositionFinder( GradedHomWp1, i );
  fi;
  Dpi:= HomKoszulDifferential( A, Wp, HomWp0i, HomWpi, p );
  Dp1i:= HomKoszulDifferential( A, Wp1, HomWpi, HomWp1i, p + 1 );
  return [ Dp1i, Dpi ];
end;





####################################################################################################################################################





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
		Add( nListB, nthGradeOfAlgebra( B, n + x1[2] ) );
	od;
	SummandList:= [ ];
	for i in [1..Length( ListA )] do
		RestrictedSubspaceGens:= HomSpaceBasis2( GradedA, B, ListA[i][1], nListB[i] );
#		HomSubspace:= Subspace( HomAB, RestrictedSubspaceGens );
		HomSubspace:= VectorSpace( K, RestrictedSubspaceGens );
		Add( SummandList, HomSubspace );
	od;
	return Sum( SummandList );
end;


HomKoszulDifferentialImage2:= function( f, Wp, A, p )  #inputs a linear map f: Wp0 = W_{p-1} -> A and
                                                #outputs the linear map Dpf: W_p -> A defined in
                                                #the paper Koszul Calculus, after using the
                                                #isomorphism Hom_{A^e}(A(x)Wp(x)A, A) = Hom_k(Wp, A)
  local Dpf, kQ, Wp0, Agens, bWp, DpfImageList, x, xLeftDecomp, xRightDecomp, i, L ;
  kQ:= Parent( Wp ); bWp:= Basis( Wp );
  Wp0:= Source( f ); #A:= Range( f );
  Agens:= GeneratorsOfAlgebra( A ); Agens:= DuplicateRemover( Agens );
  DpfImageList:= [];
  for x in bWp do
    xLeftDecomp:= LeftmostProductDecomposition( kQ, x );
    xRightDecomp:= RightmostProductDecomposition( kQ, x );
    for i in [1..Length( Agens )] do
      L:= [];
      Add( L, Agens[i]*Image( f, xLeftDecomp[i] ) + (-1)^p * Image( f, xRightDecomp[i] )*Agens[i] );
    od;
    Add( DpfImageList, Sum( L ) );
  od;
  Dpf:= LeftModuleHomomorphismByImagesNC( Wp, A, bWp, DpfImageList );
  return Dpf ;
end;


HomKoszulDifferential2:= function( A, Wp, HomWp0, HomWp, p ) #outputs Dp: Hom( Wp0, A) -> Hom( Wp, A )
  local Dp, K, Wp0, BasisHomWp0, f, ImageList ;
  K:= LeftActingDomain( A );
#  Wp0:= nthKoszulComplexObject( A, p-1 ); HomWp0:= Hom( K, Wp0, A );
#  Wp:= nthKoszulComplexObject( A, p ); HomWp:= Hom( K, Wp, A );
  BasisHomWp0:= GeneratorsOfLeftModule( HomWp0 ); ImageList:= [];
  for f in BasisHomWp0 do
    Add( ImageList, HomKoszulDifferentialImage2( f, Wp, A, p ) );
  od;
  Dp:= LeftModuleHomomorphismByImagesNC( HomWp0, HomWp, BasisHomWp0, ImageList );
  return Dp ;
end;


GradedKoszulCohomologyMaps2:= function( A, p, i )
  local K, GradedWp0, GradedWp, GradedWp1, Wp0, Wp, Wp1, HomWp0i, HomWpi, HomWp1i,
        Dpi, Dp1i ;
  K:= LeftActingDomain( A );
  GradedWp0:= GradednthKoszulComplexObject( A, p - 1 ); Wp0:= GradedWp0[1];  Print( "Wp0" );
  GradedWp:= GradednthKoszulComplexObject( A, p ); Wp:= GradedWp[1];  Print( "Wp" );
  GradedWp1:= GradednthKoszulComplexObject( A, p + 1 ); Wp1:= GradedWp1[1]; Print( "Wp1" );
  if IsFiniteDimensional( A ) = false and i = "full" then
    Error( "Cannot compute the full cohomology of an infinite-dimensional algebra (yet)");
  elif i = "full" then
    HomWp0i:= GradedHomKoszulComplexObject( GradedA, p-1 )[1] ;
    HomWpi:= GradedHomKoszulComplexObject( GradedA, p )[1] ;
    HomWp1i:= GradedHomKoszulComplexObject( GradedA, p + 1 )[1] ;
  elif IsInt( i ) = true and i > -1 then
    HomWp0i:= nthGradedHom2( K, GradedWp0, A, i ); Print( "HomWp0i" );
    HomWpi:= nthGradedHom2( K, GradedWp, A, i ); Print( "HomWpi" );
    HomWp1i:= nthGradedHom2( K, GradedWp1, A, i ); Print( "HomWp1i" );
  else
    Error( "Please enter valid inputs" );
  fi;
  Dpi:= HomKoszulDifferential2( A, Wp, HomWp0i, HomWpi, p );
  Dp1i:= HomKoszulDifferential2( A, Wp1, HomWpi, HomWp1i, p+1 );
end;
