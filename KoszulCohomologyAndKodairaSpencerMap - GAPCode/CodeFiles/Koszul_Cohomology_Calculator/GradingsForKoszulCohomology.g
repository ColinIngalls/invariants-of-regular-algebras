

LoadPackage("qpa");


#################################################################################################################################################################################


GoodListDisplay:= function( L )
	local x;
	for x in L do
		Print( x, ",\n" );
		Print( " \n" );
	od;
end;



XCustomUnion:= function( Lists )
  local x, L, U ;
  U:= [];
  for L in Lists do
    for x in L do
      if not x in U then
        Add( U, x );
      fi;
    od;
  od;
  return U;
end;



CustomUnion:= function( Lists... )
  local x, L, U ;
  if Length( Lists ) = 1 then
    U:= CallFuncList( XCustomUnion, Lists );
  else
    U:= [];
    for L in Lists do
      for x in L do
        if not x in U then
          Add( U, x );
        fi;
      od;
    od;
  fi;
  return U;
end;



TrivialLinearMap:= function( V, W )
	local f, bV, x, ImageList ;
	bV:= GeneratorsOfLeftModule( V ); ImageList:= [];
	for x in bV do
		Add( ImageList, Zero( W ) );
	od;
	f:= LeftModuleHomomorphismByImages( V, W, bV, ImageList );
	return f;
end;



IsTrue:= function( obj )
	if obj = true then
		return true;
	else
		return false;
	fi;
end;


#################################################################################################################################################################################


FreeKAlgebra:= function(K, n, indeterminate) 		#Constructs the free K-algebra on n generators as the path algbra of the n-rose
	local i, L, Arrow, nRose, KQ, variablename, identity;
	L:= [ ];
	#	identity:= StringFormatted( "1{}", indeterminate );
		identity:= StringFormatted( "{}0", indeterminate );
	if n = 0 then
		nRose:= Quiver( [ identity ], [ ] );
		KQ:= PathAlgebra( K, nRose );
		AssignGeneratorVariables( KQ );
		return KQ ;
	else
		for i in [1..n] do
			Arrow:= [ identity, identity ];
			variablename:= StringFormatted( "{}{}", indeterminate, i );
			Add( Arrow, variablename );
			Add( L, Arrow );
		od;
		nRose:= Quiver( [ identity ], L );
		KQ:= PathAlgebra( K, nRose );
		AssignGeneratorVariables( KQ );
		return KQ ;
	fi;
end;



FreeKAlgebraNoGeneratorNames:= function(K, n, indeterminate)	#Constructs the free K-algebra on n generators as the path algbra of the n-rose,
																															#but does not call AssignGeneratorVariables.
	local i, L, Arrow, nRose, KQ, variablename, identity;
	L:= [ ];
	identity:= StringFormatted( "1{}", indeterminate );
	if n = 0 then
		nRose:= Quiver( [ identity ], [ ] );
		KQ:= PathAlgebra( K, nRose );
		return KQ ;
	else
		for i in [1..n] do
			Arrow:= [ identity, identity ];
			variablename:= StringFormatted( "{}{}", indeterminate, i );
			Add( Arrow, variablename );
			Add( L, Arrow );
		od;
		nRose:= Quiver( [ identity ], L );
		KQ:= PathAlgebra( K, nRose );
		return KQ ;
	fi;
end;



GBQuotient:= function(kQ, rels)	#Unnecessary function, kept for posterity
	local gb, grb, I, A ;
	gb:= GBNPGroebnerBasis( rels, kQ );
	I:= Ideal( kQ, gb );
	GroebnerBasis( I, gb );
	A:= kQ/I;
	return A;
end;



QuadraticDualByRels:= function(KQ, Rels)		#Rels is a set of quadratic relations in the path algebra KQ. This fuction outputs the quadratic dual of KQ/(Rels)
	local gb, grb, PerpRels, kq, I, Aschrick ;
	PerpRels:= QuadraticPerpOfPathAlgebraIdeal( Rels );
	kq:= PerpRels[1];
#	I:= Ideal( kq, PerpRels[2] );
#	gb:= GroebnerBasisFunction( kq )( PerpRels[2], kq );
#	grb:= GroebnerBasis( I, gb );
#	Aschrick:= kq/I;
	Aschrick:= GBQuotient( kq, PerpRels[2] );
	AssignGeneratorVariables( Aschrick );
	return [ Aschrick, kq, PerpRels[2] ];
end;



QuadraticDualByRelsNoQuotient:= function(KQ, Rels) #Rels is a set of quadratic relations in the path algebra KQ. This fuction outputs the quadratic dual of KQ/(Rels)
	local gb, grb, PerpRels, kq, I, Aschrick ;
	PerpRels:= QuadraticPerpOfPathAlgebraIdeal( Rels );
	kq:= PerpRels[1];
#	I:= Ideal( kq, PerpRels[2] );
#	gb:= GroebnerBasisFunction( kq )( PerpRels[2], kq );
#	grb:= GroebnerBasis( I, gb );
#	Aschrick:= kq/I;
#	AssignGeneratorVariables( Aschrick );
	return [ 0, kq, PerpRels[2] ];
end;



QuadraticDual:= function( A )		#Rels is a set of quadratic relations in the path algebra KQ. This fuction outputs the quadratic dual of KQ/(Rels)
	local KQ, Rels, gb, grb, PerpRels, kq, I, Aschrick ;
	KQ:= OriginalPathAlgebra( A );
	Rels:= RelationsOfAlgebra( A );
	PerpRels:= QuadraticPerpOfPathAlgebraIdeal( Rels );
	kq:= PerpRels[1];
	I:= Ideal( kq, PerpRels[2] );
	gb:= GroebnerBasisFunction( kq )( PerpRels[2], kq );
	grb:= GroebnerBasis( I, gb );
	Aschrick:= kq/I;
	AssignGeneratorVariables( Aschrick );
	return [ Aschrick, kq, I, PerpRels[2] ];
end;



NonOneGeneratorsOfAlgebra:= function( A )	#When asked to output the generators of an algebra, GAP will often include the identity element twice.
																					#The goal of this function is to get all generators of the algebra, save for the identity.
	local Gens, NonOneGens, x ;
	Gens:= GeneratorsOfAlgebra( A );
	NonOneGens:= [ ];
	for x in Gens do
		if not x = One( A ) then
			Add( NonOneGens, x );
		fi;
	od;
	return NonOneGens ;
end;



DuplicateRemover:= function( L )  #When asked to output the generators of an algebra, GAP will often include the identity element twice.
																	#The goal of this function is to get a list of distinct generators for the algebra
  local NewL, x ;
  NewL:= [];
  for x in L do
    if not x in NewL then
      Add( NewL, x );
    fi;
  od;
  return NewL ;
end;



DuplicateChecker:= function( L )
  local l, x, L0, y ;
  l:= Length( L );
  for x in [1..l] do
    for y in [1..l] do
      if not x = y and L[x] = L[y] then
        return true ;
      fi;
    od;
  od;
  return false;
end;


#################################################################################################################################################################################


GradedBaseField:= function( K )
	return [ K, [ [ K, 0  ] ] ];
end;



GeneratorsOfNthGradedIdeal:= function( kQ, rels, n )			#This function outputs a set of generators for the subspace I \cap kQn of kQ, for a set rels of homogeneous generators of I#
	local L, i, MonomialsOfLesserDegree, V, iter, nGens, P ;
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
	for P in iter do
		if P[1]*P[2]*P[3] in V then								#checks if the product is homogeneous of degree n
			Add( nGens, P[1]*P[2]*P[3] );
		else
			continue ;
		fi;
	od;
	return nGens ;
end;



OrderedPathsOfLengthN:= function( kQ, n )
	local x, i, y, L, LList, Gens, VariableName, Cart, degreeN;
	if n = 0 then
		return [ One( kQ ) ];
	else
		L:= [ ];
		Gens:= GeneratorsOfAlgebra( kQ );
		VariableName:= Length( GeneratorsOfAlgebra( kQ ) );
		for x in Gens do
			if not x = One( kQ ) then
				Add( L, x );
			fi;
		od;
		LList:= [];
		for i in [1..n] do
			Add( LList, L );
		od;
		#Cart:= Tuples( L, n );
		Cart:= Cartesian( LList );
		degreeN:= [];
		for y in Cart do
			if not Product( y ) in degreeN and not Product( y ) = Zero( kQ ) then
				Add( degreeN, Product( y ) );
			fi;
		od;
		return degreeN ;
	fi;
end;



nthGradeOfAlgebra:= function( A, n )	#A must be a quotient of a free algebra
																			#outputted by FreeKAlgebra. This function
																			#outputs the nth graded component of A,
																			#where the grading is given by weight
	local gens, Grade;
	if n < 0 then
		Grade:= Subspace( A, [ Zero( A ) ] ); #TrivialSubspace( A );
	else
		gens:= OrderedPathsOfLengthN( A, n );
		Grade:= Subspace( A, gens );
	fi;
	return Grade ;
end;



nthGradeOfAlgebraByRels:= function( kQ, rels, n )	#This function outputs the nth graded
																									#component of kQ/rels, where the grading
																									#is given by weight
	local gens, ngens, kQn, nthSubspace, Grade;
	if n < 0 then
		Grade:= Subspace( kQ, [ Zero( kQ ) ] ); #TrivialSubspace( A );
	else
		gens:= OrderedPathsOfLengthN( kQ, n );
		kQn:= Subspace( kQ, gens );
		ngens:= GeneratorsOfNthGradedIdeal( kQ, rels, n );
		nthSubspace:= Subspace( kQn, ngens );
		Grade:= kQn/nthSubspace;
	fi;
	return Grade ;
end;



GradingOfAlgebra:= function( A )    #This function assumes that the ideal generated by rels intersects kQ_0 trivially and that rels is a set of homogeneous relations of kQ
	local Counter, I, kQ, rels, DimTotal, ComponentList, DimOfComponents, gens, Grade ;
	if IsFiniteDimensional( A ) = true then
		DimTotal:= Dimension( A );
		ComponentList:= [ ];
		DimOfComponents:= [ ];
		Counter:= 0 ;
		while Sum( DimOfComponents ) < DimTotal do
			Grade:= nthGradeOfAlgebra( A, Counter );
			Add( ComponentList, [ Grade, Counter ] );
			Add( DimOfComponents, Dimension( Grade ) );
			Counter:= Counter + 1;
		od;
		if Sum( DimOfComponents ) = DimTotal then
			return [ A, ComponentList ] ;
		else
			return [ A, ComponentList, "The relations may not be homogeneous" ];
		fi;
	else
		Print("The algebra is not finite dimensional");
	fi;
end;



GradedPositionFinder:= function( GradedA, n )
	local x, ListA, L;
	L:= [ ];
	ListA:= GradedA[2];
	for x in ListA do
		if x[2] = n then
			Add( L, x[1] );
		fi;
	od;
	if L = [ ] then
		return TrivialSubspace( GradedA[1] );
	else
		return L[1];
	fi;
end;



GradedDimensionVerifier:= function( GradedA )
	local x, A, ListA, ListOfDims;
	A:= GradedA[1]; ListA:= GradedA[2];
	ListOfDims:= [ ];
	for x in ListA do
		Add( ListOfDims, Dimension( x[1] ) ) ;
	od;
	return [ Dimension( A ), Sum( ListOfDims ) ];
end;



GradedConditionVerifier:= function( GradedA )
	local ListA, cart, x, L, ProdSpace;
	ListA:= GradedA[2] ;
	cart:= IteratorOfCartesianProduct( ListA, ListA );
	L:= [];
	for x in cart do
		ProdSpace:= ProductSpace( x[1][1], x[2][1] );
		if not ProdSpace = GradedPositionFinder( GradedA, x[1][2] + x[2][2] ) then
			Add( L, x );
		fi;
#		Add( L, ProductSpace( x[1][1], x[2][1] ) = GradedPositionFinder( GradedA, x[1][2] + x[2][2] ) );
	od;
#	return ForAll( L, IsTrue );
	return L ;
end;



GradedSubset:= function( GradedA, SubsetOfA )
	local A, GradedSubset, GradedPart, x ;
	A:= GradedA[1];
	GradedSubset:= [ SubsetOfA ];
	GradedPart:= [ ];
	for x in GradedA[2] do
		Add( GradedPart, [ Intersection( x[1], SubsetOfA ), x[2] ] ) ;
	od;
	Add( GradedSubset, GradedPart );
	return GradedSubset ;
end;



BasisForGradedAlgebra:= function( GradedA )
	local A, L, x, NewBase;
	A:= GradedA[1];
	L:= [];
	for x in GradedA[2] do
		Add( L, Basis( x[1] ) );
	od;
	NewBase:= Basis( A, CustomUnion( L ) );
	return NewBase;
end;



HilbertSeriesOfGradedAlgebra:= function( A, MinGrade, MaxGrade )
	local grades, dims, n, An ;
	grades:= [MinGrade..MaxGrade] ;
	dims:= [];
	for n in grades do
		An:= nthGradeOfAlgebra( A, n );
		Add( dims, Dimension( An ) );
	od;
	return dims;
end;



HilbertSeriesOfGradedAlgebraByRels:= function( kQ, rels, MinGrade, MaxGrade )
	local grades, dims, n, An ;
	grades:= [MinGrade..MaxGrade] ;
	dims:= [];
	for n in grades do
		An:= nthGradeOfAlgebraByRels( kQ, rels, n );
		Add( dims, Dimension( An ) );
	od;
	return dims;
end;



MinMaxDegreeOfGradedAlgebra:= function( GradedA )
	local ListA, IndexA, x, Amin, Amax;
	if IsFiniteDimensional( GradedA[1] ) then
		ListA:= GradedA[2];
		IndexA:= [ ];
		for x in ListA do
			Add( IndexA, x[2] );
		od;
		Amin:= Minimum( IndexA ); Amax:= Maximum( IndexA );
		return [ Amin, Amax ];
	else
		Error( "The algebra must be finite-dimensional" );
	fi;
end;



BasisForGradedAlgebra:= function( GradedA )
	local A, L, x, NewBase;
	A:= GradedA[1];
	L:= [];
	for x in GradedA[2] do
		Add( L, BasisVectors( Basis( x[1] ) ) );
	od;
	NewBase:= Basis( A, Union( L ) );
	return NewBase;
end;


#################################################################################################################################################################################


IsMapOfDegreeN:= function( f, GradedA, GradedB, n )
	local A, B, ListA, ListB, NewListB, IndexA, IndexB, Amin, Amax, Bmin, Bmax, c, x1, x2, x3, x4, x5, x6, i, MaxCounter, MinCounter, ImageList, L, TruthList, t ;
	A:= GradedA[1]; ListA:= GradedA[2];
	B:= GradedB[1]; ListB:= GradedB[2];
#
	IndexA:= [ ]; IndexB:= [ ];
	for x1 in ListA do
		Add( IndexA, x1[2] );
	od;
	Amin:= Minimum( IndexA ); Amax:= Maximum( IndexA );
#
	for x2 in ListB do
		Add( IndexB, x2[2] );
	od;
	Bmin:= Minimum( IndexB ); Bmax:= Maximum( IndexB );
#
	MaxCounter:= Bmax + 1; MinCounter:= Bmin - 1;
	NewListB:= ShallowCopy( ListB );
	c:= Length( ListA ) + AbsInt(n)*2;
	for x3 in [1..c] do												#Need to add a considerable amount of trivial graded parts to B to make the function verify degree well
		Add( NewListB, [ TrivialSubspace( B ), MaxCounter ] );
		Add( NewListB, [ TrivialSubspace( B ), MinCounter ] );
		MaxCounter:= MaxCounter + 1; MinCounter:= MinCounter - 1;
	od;
#
	ImageList:= [ ];
	for i in [Amin..Amax] do										#This part makes pairs [ B_{i+n}, f(Ai) ], for graded parts Bj and Ai of B and A, respectively, so that
		L:= [ ];																	#we may use IsSubset afterwards on this list.
		for x4 in NewListB do
			if x4[2] = n + i then
				Add( L, x4[1] );
			else
				continue;
			fi;
		od;
		for x5 in ListA do
			if x5[2] = i then
				Add( L, Image( f, x5[1] ) );
			else
				continue;
			fi;
		od;
		Add( ImageList, L );
	od;
#
	TruthList:= [ ];												#This part is needed since the ForAll function only works on unary functions
	for x6 in ImageList do
		Add( TruthList, IsSubset( x6[1], x6[2] ) );
	od;
	t:= ForAll( TruthList, IsTrue );
return t;
end;


#################################################################################################################################################################################


HomSpaceBasisByTuples:= function( A, B, BaseA, BaseB )  #Returns a basis for the subspace Hom(Ai, Bj) of Hom(A, B), without explicitly computing the subspace
	local x1, i, cart, L, f, HomBase ;
	cart:= IteratorOfCartesianProduct( BaseA, BaseB );
	HomBase:= [ ];
	for x1 in cart do
		i:= Position( BaseA, x1[1] );
		L:= [];
		CopyListEntries( [ Zero( B ) ], 1, 0, L, 1, 1, Length( BaseA ) );   #This is to define the map sending the basis element x1[1] to x1[2], and all
		L[i]:= x1[2];																												#other basis elements to 0
		f:= LeftModuleHomomorphismByImages( A, B, BaseA, L );
		Add( HomBase, f );
	od;
	return HomBase;
end;



HomSpaceBasis:= function( GradedA, GradedB, Ai, Bj)  #Returns a basis for the subspace Hom(Ai, Bj) of Hom(A, B), without explicitly computing the subspace
	local x1, i, A, B, bA, bAi, bBj, cart, L, f, HomBase ;
	A:= GradedA[1]; B:= GradedB[1];
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



nthGradedHom:= function( K, HomAB, GradedA, GradedB, n )   #This function outputs the nth graded Hom set Hom( A, B )_n of linear maps A -> B of degree n
	local i, x1, f, A, B, ListA, ListB, BaseHomAB, nListB, RestrictedSubspaceGens, HomSubspace, SummandList;
	A:= GradedA[1]; ListA:= GradedA[2]; BaseHomAB:= Basis( HomAB );
	B:= GradedB[1]; ListB:= GradedB[2];
	nListB:= [ ];
	for x1 in ListA do
		Add( nListB, GradedPositionFinder( GradedB, n + x1[2] ) );
	od;
	SummandList:= [ ];
	for i in [1..Length( ListA )] do
		RestrictedSubspaceGens:= HomSpaceBasis( GradedA, GradedB, ListA[i][1], nListB[i] );
		HomSubspace:= Subspace( HomAB, RestrictedSubspaceGens );
		Add( SummandList, HomSubspace );
	od;
	return Sum( SummandList );
end;



HOMGrading:= function( K, GradedA, GradedB ) #This function returns the grading of HOM(A, B) = \bigoplus_{n \in \mathbb{Z}} Hom(A, B)_n
	local n, x1, x2, x3, x4, x5, A, B, HomAB, ListA, ListB, IndexA, IndexB, Amin, Amax, Bmin, Bmax, MaxCounter, MinCounter, HOMMax, HOMMin, HomGrades, nGrade ;
	A:= GradedA[1]; ListA:= GradedA[2];
	B:= GradedB[1]; ListB:= GradedB[2];
	HomAB:= Hom( K, A, B );
	IndexA:= [ ]; IndexB:= [ ];
#
	for x1 in ListA do
		Add( IndexA, x1[2] );
	od;
	Amin:= Minimum( IndexA ); Amax:= Maximum( IndexA );
#
	for x2 in ListB do
		Add( IndexB, x2[2] );
	od;
	Bmin:= Minimum( IndexB ); Bmax:= Maximum( IndexB );
#
	HOMMax:= Bmax - Amin; HOMMin:= Bmin - Amax;
	HomGrades:= [ ];
	for n in [HOMMin..HOMMax] do
		nGrade:= nthGradedHom( K, HomAB, GradedA, GradedB, n );
		Add( HomGrades, [ nGrade, n ] );
	od;
	return [ HomAB, HomGrades ];
end;
