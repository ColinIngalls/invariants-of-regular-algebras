

sayhello:= function()
	Print("Hello, world.\n");
end;

######################################################################################################################################################################################

Lexi:= function(A, k, l)					#Order isomorphism between {1, ..., n^2} and {1, ..., n}^2 with the lexicographic order#
	return (l - 1)*Dimension(A) + k ;		#Also serves as an isomorphism {1, ..., nm} -> {1, ..., n}x{1, ..., m} with the lexicographic order#
end;



ixeL:= function(A, m)						#Inverse function to Lexi#
	local d ;
	d:= Dimension( A );
	return [ ( ( m - 1 ) mod d ) + 1, 1 + ( ( m - 1 ) - ( ( m - 1 ) mod d ) )/d ] ;
end;



Lexi2:= function(DimB, k, l)
	return ( k - 1 )*DimB + l ;
end;



2ixeL:= function( DimB, a )
	return [ 1 + ( ( a - 1 ) - ( ( a - 1 ) mod DimB ) )/DimB, ( ( a - 1) mod DimB ) + 1 ] ;
end;



tuple:= function( arg...)
	return arg;
end;


######################################################################################################################################################################################

EntryLoop:= function(A, i1, j1, i2, j2)							#generates the structure coefficient of the products of basis tensors (e_{i1} \otimes e_{j1})(e_{i2} \otimes e_{j2})
	local L, T, k, l, Z1, Z2 ;
	L:= [ ] ;
	T:= StructureConstantsTable( Basis( A ) );
	Z1 := Length( T[i1][j1][1] );
	Z2 := Length( T[i2][j2][1] );
	for k in [1..Z1] do
		for l in [1..Z2] do
			if not T[i1][j1][2][k]*T[i2][j2][2][l] = 0 then				#Verifies if the product is nonzero
				Add( L, T[i1][j1][2][k]*T[i2][j2][2][l] );				#If the product is nonzero, adds it to the list
				Add( L, Lexi(A, T[i1][j1][1][k], T[i2][j2][1][l] ) );	#Adds the coefficient position to the list
			else
				continue;												#If product is zero, does nothing
			fi;
		od;
	od;
	return L;
end;



TensorProd:= function(A)
	local T, DA, BA, TabTenA, TenA, L, i, j ;
	DA:= Dimension( A );
	T:= StructureConstantsTable( Basis( A ) );
	TabTenA:= EmptySCTable( Dimension( A )^2, Zero( LeftActingDomain( A ) ) ) ;
	for i in [1..DA^2] do
		for j in [1..DA^2] do					#For each pair of basis elements, add the list of nonzero structure coefficients to the table TA
			L:= EntryLoop(A, ixeL( A, i )[1], ixeL( A, j )[1], ixeL( A, i )[2], ixeL( A, j )[2] ) ;
			SetEntrySCTable( TabTenA, i, j, L ) ;
		od ;
	od;
	TenA:= AlgebraByStructureConstants( LeftActingDomain( A ), TabTenA );
	return TenA ;
end;
###### Not what I want, I need to be able to take the tensor product of two arbitrary algebras


######################################################################################################################################################################################


#nEntryLoop:= function(AlgList, i, j)									#generates the structure coefficients of the products of the ith and jth basis elements of the tensor product
#	local N, L, Dims, Structure, A, Indices, NonZeroList, NonZeros, NonZeroCoeff, NonZeroCoeffTuples, k, T, a ;
#	N:= Length( AlgList );
#	L:= [ ] ;
#	Dims:= [ ] ;
#	Structure:= [ ];
#	for A in AlgList do
#		Add( Dims, [1..Dimension(A)] );
#		Add( Structure, StructureConstantsTable( Basis( A ) ) );
#	od;
#	Add( Dims, tuple );
#	Indices:= CallFuncList( ListX, Dims ) ;			#Makes a table that will serve to locate the position of basis vectors of the tensor product
#	NonZeroList:= [ ] ;
#	NonZeroCoeff:= [ ] ;
#	for k in [1..N] do
#		T:= Structure[k] ;
#		Add( NonZeroList, T[ Indices[i][k] ][ Indices[j][k] ][1] );
#		Add( NonZeroCoeff, T[ Indices[i][k] ][ Indices[j][k] ][2] );
#	od;
#	Add( NonZeroList, tuple );
#	Add( NonZeroCoeff, tuple );
#	NonZeros:= CallFuncList( ListX, NonZeroList );						#Stores the indices of the nonzero structure coefficients in the structure constant tables
#	NonZeroCoeffTuples:= CallFuncList( ListX, NonZeroCoeff );			#Stores the values of the nonzero structure coefficients as lists
#	 for a in [1..Length(NonZeros)] do
#		Add( L, Product( NonZeroCoeffTuples[a] ) );						#Adds the nonzero products of structure constants to the list L
#		Add( L, Position( Indices, NonZeros[a] ) );						#Adds the position of said products
#	od;
#	return L ;
#end;



#TensorTest:= function( AlgList... )
#	local L, DimList, A, TensorDim, TabTensor, Dims, Indices, i, j, Tensor ;
#	DimList:= [ ] ;
#	for A in AlgList do
#		Add( DimList, Dimension( A ) );
#	od;
#	TensorDim:= Product( DimList );
#	TabTensor:= EmptySCTable( TensorDim, Zero( LeftActingDomain( AlgList[1] ) ) );
#	for i in [1..TensorDim] do
#		for j in [1..TensorDim] do
#			L:=nEntryLoop( AlgList, i, j );
#			SetEntrySCTable( TabTensor, i, j, L );
#		od;
#	od;
#	Tensor:= AlgebraByStructureConstants( LeftActingDomain( AlgList[1] ), TabTensor );
#	return Tensor ;
#end;



######################################################################################################################################################################################


#EntryLoop2:= function(A, B, i1, j1, i2, j2)									#generates the structure coefficient of the products of basis tensors (e_{i1} \otimes b_{j1})(e_{i2} \otimes b_{j2})
#	local L, TA, TB, k, l, Z1, Z2, Indices, NonZeros, x, Pos ;
#	L:= [ ] ;
#	TA:= StructureConstantsTable( Basis( A ) );
#	TB:= StructureConstantsTable( Basis( B ) );
#	Indices:= ListX( [1..Dimension(A)], [1..Dimension(B)], tuple );
#	Z1 := Length( TA[i1][i2][1] );
#	Z2 := Length( TB[j1][j2][1] );
#	NonZeros:= ListX( [1..Z1], [1..Z2], tuple );
#	for x in NonZeros do
#		if not TA[i1][i2][2][x[1]]*TB[j1][j2][2][x[2]] = 0 then								#Verifies if the product is nonzero
#				Add( L, TA[i1][i2][2][x[1]]*TB[j1][j2][2][x[2]] );							#If the product is nonzero, adds it to the list
#				Pos:= Position( Indices, [ TA[i1][i2][1][x[1]], TB[j1][j2][1][x[2]] ] ) ;
#				Add( L, Pos );																#Adds the coefficient position to the list
#			else
#				continue;													#If product is zero, does nothing
#		fi;
#	od;
#	return L;
#end;



#TensorProd2:= function(A, B)
#	local T, DA, DB, TabTensor, Indices, Indices2, Tensor, BasisNames, L, x, y, Pos1, Pos2 ;
#	if LeftActingDomain( A ) = LeftActingDomain( B ) then
#		DA:= Dimension( A );
#		DB:= Dimension( B );
#		T:= StructureConstantsTable( Basis( A ) );
#		TabTensor:= EmptySCTable( DA*DB, Zero( LeftActingDomain( A ) ) ) ;
#		Indices:= ListX( [1..DA], [1..DB], tuple );
#		Indices2:= ListX( Indices, Indices, tuple) ;
#		BasisNames:= [] ;
#		for x in Indices2 do
#			L:= EntryLoop2(A, B, x[1][1], x[1][2], x[2][1], x[2][2] );
#			Pos1:= Position(Indices, x[1] );
#			Pos2:= Position(Indices, x[2] );
#			SetEntrySCTable( TabTensor, Pos1, Pos2, L ) ;
#		od;
#		for y in Indices do
#			Add( BasisNames, StringFormatted( "{} (x) {}", Basis(A)[y[1]], Basis(B)[y[2]] ) );
#		od;
#		Tensor:= AlgebraByStructureConstants( LeftActingDomain( A ), TabTensor, BasisNames );
#		return Tensor ;
#	else
#		Print("The inputted algebras are not defined over the same field") ;
#	fi;
#end;


######################################################################################################################################################################################


EntryLoop2:= function(A, B, i1, j1, i2, j2)									#generates the structure coefficient of the products of basis tensors (e_{i1} \otimes b_{j1})(e_{i2} \otimes b_{j2})
	local L, TA, TB, k, l, Z1, Z2 ;
	L:= [ ] ;
	TA:= StructureConstantsTable( Basis( A ) );
	TB:= StructureConstantsTable( Basis( B ) );
	Z1 := Length( TA[i1][i2][1] );
	Z2 := Length( TB[j1][j2][1] );
	for k in [1..Z1] do
		for l in [1..Z2] do
			if not TA[i1][i2][2][k]*TB[j1][j2][2][l] = 0 then				#Verifies if the product is nonzero
				Add( L, TA[i1][i2][2][k]*TB[j1][j2][2][l] );				#If the product is nonzero, adds it to the list
				Add( L, Lexi(A, TA[i1][i2][1][k], TB[j1][j2][1][l] ) );		#Adds the coefficient position to the list
			else
				continue;													#If product is zero, does nothing
			fi;
		od;
	od;
	return L;
end;



#TensorProd2:= function(A, B)
#	local T, DA, DB, TabTensor, Tensor, BasisNames, L, i, j ;
#	if LeftActingDomain( A ) = LeftActingDomain( B ) then
#		DA:= Dimension( A );
#		DB:= Dimension( B );
#		T:= StructureConstantsTable( Basis( A ) );
#		TabTensor:= EmptySCTable( DA*DB, Zero( LeftActingDomain( A ) ) ) ;
#		BasisNames:= [] ;
#		for i in [1..DA*DB] do
#			for j in [1..DA*DB] do					#For each pair of basis elements, add the list of nonzero structure coefficients to the table TabTensor
#				L:= EntryLoop2(A, B, ixeL( A, i )[1], ixeL( A, i )[2], ixeL( A, j )[1], ixeL( A, j )[2] ) ;
#				SetEntrySCTable( TabTensor, i, j, L ) ;
#			od ;
#		od;
#		for i in [1..DB] do
#			for j in [1..DA] do
#				Add( BasisNames, StringFormatted( "{} (x) {}", Basis(A)[j], Basis(B)[i] ) );
#			od;
#		od;
#		Tensor:= AlgebraByStructureConstants( LeftActingDomain( A ), TabTensor, BasisNames );
#		return Tensor ;
#	else
#		Print("The inputted algebras are not defined over the same field") ;
#	fi;
#end;


TensorProd2:= function(A, B)
	local T, DA, DB, TabTensor, Tensor, L, i, j ;
	if LeftActingDomain( A ) = LeftActingDomain( B ) then
		DA:= Dimension( A );
		DB:= Dimension( B );
		T:= StructureConstantsTable( Basis( A ) );
		TabTensor:= EmptySCTable( DA*DB, Zero( LeftActingDomain( A ) ) ) ;
		for i in [1..DA*DB] do
			for j in [1..DA*DB] do					#For each pair of basis elements, add the list of nonzero structure coefficients to the table TabTensor
				L:= EntryLoop2(A, B, ixeL( A, i )[1], ixeL( A, i )[2], ixeL( A, j )[1], ixeL( A, j )[2] ) ;
				SetEntrySCTable( TabTensor, i, j, L ) ;
			od ;
		od;
		Tensor:= AlgebraByStructureConstants( LeftActingDomain( A ), TabTensor);
		return Tensor ;
	else
		Print("The inputted algebras are not defined over the same field") ;
	fi;
end;


######################################################################################################################################################################################

#nTensors:= function(A, n)				#THIS IS NOT RECURSION YOU DUMMY!#
#	local Prod, R, i ;
#	if n >= 2 then
#		Prod:= TensorProd2( A, A ) ;
#		for  i in [2..n] do
#			R:= TensorProd2( A, Prod ) ;
#			Prod:= R ;
#		od;
#		return Prod ;
#	elif n = 0 then
#		return LeftActingDomain( A ) ;
#	elif n = 1 then
#		return A ;
#	else
#		Print( "Please input nonnegative integers" );
#	fi;
#end;



nTensors:= function(A, n)
	local Prod, R, i ;
	if n < 0 then
		Print("This is not defined for negative integers");
	elif n = 0 then
		return LeftActingDomain( A );
	elif n = 1 then
		return A ;
	elif n = 2 then
		return TensorProd2( A, A );
	elif n > 2 then
		Prod:= TensorProd2( nTensors( A, n-1 ), A );
		return Prod ;
	fi;
end;


#I think the basis defined by TensorProd2 is wrong (mislabelled)#
#TensorTest:= function( AlgList )
#	local Prod, A, NewList, n ;
#	n:= Length( AlgList );
#	if n < 0 then
#		Print("This is not defined for negative integers");
#	elif n = 0 then
#		return LeftActingDomain( AlgList[1] );
#	elif n = 1 then
#		return AlgList[1] ;
#	elif n > 1 then
#		A:= AlgList[n];
#		NewList:= AlgList{[1..(n-1)]};
#		Prod:= TensorProd2( TensorTest( NewList ), A );
#		return Prod ;
#	fi;
#?end;


######################################################################################################################################################################################


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
				Add( L, Pos );  															#Adds the coefficient position to the list
			else
				continue;																	#If product is zero, does nothing
			fi;
		od;
	od;
	return L;
end;


SCTableBuilder:= function(TableA, TableB, zero)				#This function inputs the structure constant table of two algebras and outputs the structure
	local TabTensor, LA, LB, i, j, L, PositionPairs ;						#constant table of their tensor products
	LA:= Length( TableA )-2;
	LB:= Length( TableB )-2;
	TabTensor:= EmptySCTable( LA*LB, zero );
	PositionPairs:= Cartesian( [1..LA*LB], [1..LA*LB] );
	for i in PositionPairs do
		L:= BetterEntryLoop3(TableA, TableB, 2ixeL( LB, i[1] )[1], 2ixeL( LB, i[1] )[2], 2ixeL( LB, i[2] )[1], 2ixeL( LB, i[2] )[2] ) ;
		SetEntrySCTable( TabTensor, i[1], i[2], L ) ;
	od ;
	return TabTensor ;
end;


RecursiveSCTableBuilder:= function( Tables, zero ) #Tables must be a list of structure constant tables
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

TensorBasis2:= function( BasisA, BasisB )			#Trying to represent the basis of the tensor product as pairs "a (x) b"
	local BasisPairs, TenBasis, x ;
	BasisPairs:= Cartesian( BasisA, BasisB );
	TenBasis:= [ ];
	for x in BasisPairs do
		Add( TenBasis, StringFormatted( " {} (x) {} ", x[1], x[2] ) );
	od;
	return TenBasis ;
end;

nTensorBasis:= function( Bases )
	local SmallerBases, n, TenBasis1, TenBasis, Bn ;
	n:= Length(Bases);
	if n = 1 then
		TenBasis:= Bases ;
	elif n = 2 then
		TenBasis:= TensorBasis2( Bases[1], Bases[2] );
	elif n > 2 then
		SmallerBases:= Bases{[1..(n-1)]};
		Bn:= Bases[n];
		TenBasis1:= nTensorBasis( SmallerBases );
		TenBasis:= TensorBasis2( TenBasis1, Bn );
	fi;
	return TenBasis ;
end;


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
	TensorBasis:= nTensorBasis( Bases );
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


#CustomSimpleTensor:= function( ListOfElms, ATensB, A, B )
#	local x, a, b, ab, BasisA, BasisB, BasisAB, aCoeff, bCoeff, FakeabCoeff, abCoeff;
#	a:= ListOfElms[1]; b:= ListOfElms[2];
#	BasisA:= Basis( A ); BasisB:= Basis( B );
#	aCoeff:= Coefficients( BasisA, a ); bCoeff:= Coefficients( BasisB, b );
#	FakeabCoeff:= Cartesian( aCoeff, bCoeff );
#	abCoeff:= [ ];
#	for x in FakeabCoeff do
#		Add( abCoeff, x[1]*x[2] );
#	od;
#	BasisAB:= Basis( ATensB );
#	ab:= LinearCombination( BasisAB, abCoeff );
#	return ab;
#end;


######################################################################################################################################################################################


nTensorBasisTuples:= function(A, n)
	local i, ToBeListed, BasisA, nBasis;
	ToBeListed:= [ ];
	BasisA:= Basis( A );
	for i in [1..n] do
		Add( ToBeListed, BasisA );
	od;
	Add( ToBeListed, tuple );
	nBasis:= CallFuncList( ListX, ToBeListed );
	return nBasis ;
end;


######################################################################################################################################################################################


TestHom:= function(f, A)																		#inputs a linear map f and a vector space A#
	local HomDomain, HomRange, BRan, x, ImOfBasis, Homf ;
	if IsGeneralMapping( f ) = false then
		Print("The mapping is not linear or is not a mapping") ;
	elif not LeftActingDomain( A ) = LeftActingDomain( Source( f ) ) and not LeftActingDomain( A ) = LeftActingDomain( Range( f ) ) then ;
		Print("The vector spaces are not over the same field") ;
	else
		ImOfBasis:= [] ;
		HomDomain:= Hom( LeftActingDomain( Source( f ) ), Source( f ), A );
		HomRange:= Hom( LeftActingDomain( Range( f ) ), Range( f ), A );
		BRan:= Basis( HomRange );
		for x in BRan do															#Sends a linear map g: Range( f ) -> A in the basis to the map gf: Source( f ) -> A#
			Add( ImOfBasis, CompositionMapping( x, f ) ) ;
		od;
		Homf:= LeftModuleHomomorphismByImages( HomRange, HomDomain, BRan, ImOfBasis ) ;
		return Homf ;
	fi;
end;



######################################################################################################################################################################################
