


Lexi2:= function(DimB, k, l)                             #Order isomorphism between {1, ..., n^2} and {1, ..., n}^2 with the lexicographic order, for n = DimB#
	return ( k - 1 )*DimB + l ;                            #Also serves as an isomorphism {1, ..., nm} -> {1, ..., m}x{1, ..., n} with the lexicographic order#
end;																										 #Also also an isomorphism \mathbb{N} -> \mathbb{N}x{1, ..., n}, with lexicographic ordering


2ixeL:= function( DimB, a )                               #Is the inverse function to Lexi2
	return [ 1 + ( ( a - 1 ) - ( ( a - 1 ) mod DimB ) )/DimB, ( ( a - 1) mod DimB ) + 1 ] ;
end;

#########################################################################################################################################################

BetterEntryLoop2:= function(TA, TB, i1, i2, j1, j2)							#generates the structure coefficient of the products of basis tensors (e_{i1} \otimes b_{i2})(e_{j1} \otimes b_{j2})
	local L, k, l, Z1, Z2, Indices, Pos ;
	L:= [ ] ;
	Z1 := Length( TA[i1][j1][1] );
	Z2 := Length( TB[i2][j2][1] );
	for k in [1..Z1] do
		for l in [1..Z2] do
			if not TA[i1][j1][2][k]*TB[i2][j2][2][l] = 0 then								#Verifies if the product is nonzero (This step can probably be skipped, as we are working over a field)
				Add( L, TA[i1][j1][2][k]*TB[i2][j2][2][l] );									#If the product is nonzero, adds it to the list
				Pos:= Lexi2( Length(TB)-2, TA[i1][j1][1][k], TB[i2][j2][1][l] ) ;
				Add( L, Pos );  														                 	#Adds the coefficient position to the list
			else
				continue;																	                    #If product is zero, does nothing
			fi;
		od;
	od;
	return L;
end;


SCTableBuilder:= function(TableA, TableB, zero)				         #This function inputs the structure constant table of two algebras and outputs the structure
	local TabTensor, LA, LB, i, j, L, PositionPairs ;						#constant table of their tensor products
	LA:= Length( TableA )-2;
	LB:= Length( TableB )-2;
	TabTensor:= EmptySCTable( LA*LB, zero );
	PositionPairs:= Cartesian( [1..LA*LB], [1..LA*LB] );
	for i in PositionPairs do
		L:= BetterEntryLoop2(TableA, TableB, 2ixeL( LB, i[1] )[1], 2ixeL( LB, i[1] )[2], 2ixeL( LB, i[2] )[1], 2ixeL( LB, i[2] )[2] ) ;
		SetEntrySCTable( TabTensor, i[1], i[2], L ) ;
	od ;
	return TabTensor ;
end;


RecursiveSCTableBuilder:= function( Tables, zero )            #Tables must be a list of structure constant tables,
	local n, SmallerList, TabTensor, Tn ;
	n:= Length( Tables );
	if n = 1 then
		return Tables[1] ;
	elif n > 1 then
		Tn:= Tables[n];
		SmallerList:= Tables{[1..(n-1)]};
		TabTensor:= SCTableBuilder( RecursiveSCTableBuilder( SmallerList, zero ), Tn, zero ) ;
		return TabTensor ;
	else
		Print("Something went wrong with the RecursiveSCTableBuilder");
	fi;
end;

#########################################################################################################################################################

TensorBasisNames2:= function( BasisA, BasisB )			#This function outputs a basis for the tensor product of algebras as pairs "a (x) b", for a in BasisA and b in BasisB
	local BasisPairs, TenBasis, x ;
	BasisPairs:= Cartesian( BasisA, BasisB );
	TenBasis:= [ ];
	for x in BasisPairs do
		Add( TenBasis, StringFormatted( "{} (x) {}", x[1],  x[2] ) );
	od;
	return TenBasis ;
end;

nTensorBasisNames:= function( Bases )            #Does the same as TensorBasisNames2, but for an arbitrary list of bases
	local SmallerBases, n, TenBasis1, TenBasis, Bn ;
	n:= Length(Bases);
	if n = 1 then
		TenBasis:= Bases ;
	elif n = 2 then
		TenBasis:= TensorBasisNames2( Bases[1], Bases[2] );
	elif n > 2 then
		SmallerBases:= Bases{[1..(n-1)]};
		Bn:= Bases[n];
		TenBasis1:= nTensorBasisNames( SmallerBases );
		TenBasis:= TensorBasisNames2( TenBasis1, Bn );
	fi;
	return TenBasis ;
end;

#########################################################################################################################################################

#BEST VERSION OF THE TENSOR PRODUCT THUS FAR#
AlgebraTensorProduct:= function( Algebras... )
	local A, Bases, BasesPairs, Tables, TabTensor, Tensor, TensorBasis, B ;
	Bases:= [ ];
	Tables:= [ ];
	for A in Algebras do
		Add( Bases, Basis( A ) );
		Add( Tables, StructureConstantsTable( Basis( A ) ) );
	od;
	TabTensor:= RecursiveSCTableBuilder( Tables, Zero( LeftActingDomain( Algebras[1] ) ) );
	TensorBasis:= nTensorBasisNames( Bases );
	Tensor:= AlgebraByStructureConstants( LeftActingDomain( Algebras[1] ), TabTensor, TensorBasis );
	return Tensor ;
end;

nAlgebraTensorProduct:= function( A, n)
	local i, AlgList, Prod ;
	AlgList:= [ ];
	for i in [1..n] do
		Add( AlgList, A );
	od;
	Prod:= CallFuncList( AlgebraTensorProduct, AlgList );
	return Prod ;
end;

#########################################################################################################################################################

CustomSimpleTensor:= function( ListOfElms, ATensB, A, B )  #Takes in a list [a, b] of elements of A and B, respectively, and outputs the tensor a(x)b
	local x, a, b, ab, BasisA, BasisB, BasisAB, aCoeff, bCoeff, FakeabCoeff, abCoeff;
	a:= ListOfElms[1]; b:= ListOfElms[2];
	BasisA:= Basis( A ); BasisB:= Basis( B );
	aCoeff:= Coefficients( BasisA, a ); bCoeff:= Coefficients( BasisB, b );
	FakeabCoeff:= Cartesian( aCoeff, bCoeff );
	abCoeff:= [ ];
	for x in FakeabCoeff do
		Add( abCoeff, x[1]*x[2] );
	od;
	BasisAB:= Basis( ATensB );
	ab:= LinearCombination( BasisAB, abCoeff );
	return ab;
end;


nCustomSimpleTensor:= function( L, TensorProd, AlgList ) #L is a list of n elements a_n of A, and Tensor is the n-fold tensor product of A, as outputted by TensorProductOfAlgebraNTimes
	local A, i, x, TensorBase, BaseList, FakeTensorBase, FakeCoeffList, CartCoeffs, TensorCoeffList, TensorElm ;
	TensorBase:= Basis( TensorProd );
	BaseList:= [ ];
	for A in AlgList do
		Add( BaseList, Basis( A ) );
	od;
	FakeTensorBase:= Cartesian( BaseList );
	FakeCoeffList:= [ ];
	for i in [1..Length( L )] do
		Add( FakeCoeffList, Coefficients( Basis( AlgList[i] ), L[i] ) );
	od;
	CartCoeffs:= Cartesian( FakeCoeffList );
	TensorCoeffList:= [ ];
	for x in CartCoeffs do
		Add( TensorCoeffList, Product( x ) );
	od;
	TensorElm:= LinearCombination( TensorBase, TensorCoeffList );
	return TensorElm;
end;


TensorProductBasis:= function( BasisList, TensorProd, AlgList)
	local x, BaseTuples, FakeTensorBasis, TensorBasis;
	BaseTuples:= IteratorOfCartesianProduct( BasisList );
	FakeTensorBasis:= [];
	for x in BaseTuples do
		Add( FakeTensorBasis, nCustomSimpleTensor( x, TensorProd, AlgList ) );
	od;
	TensorBasis:= Basis( TensorProd, FakeTensorBasis );
	return TensorBasis ;
end;


TensorProductBasisNTimes:= function( n, BasisA, TensorProd, A ) #Computes a basis of A^{\otimes n} from a basis BasisA of A
	local BasisList, i, AlgList, TensorBasis;
	BasisList:= []; AlgList:= [];
	for i in [1..n] do
		Add( BasisList, BasisA );
		Add( AlgList, A );
	od;
	TensorBasis:= TensorProductBasis( BasisList, TensorProd, AlgList );
	return TensorBasis ;
end;
