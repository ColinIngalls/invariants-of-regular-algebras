
#Here is the code I have been working on. The function that was supposed to compute the cohomology is the CoHHomology function, although
#is not currently functional. I have tried to comment the code as much as possible, but some parts may still be very unclear. Do not hesitate
#to ask me if you have any questions about my code.
# - Félix L.



LoadPackage("qpa");


FreeKAlgebra:= function(K, n, indeterminate) 		#Constructs the free K-algebra on n generators as the path algbra of the n-rose
	local i, L, Arrow, nRose, KQ, variablename, identity;
	L:= [ ];
	identity:= StringFormatted( "1{}", indeterminate );
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

GBQuotient:= function(kQ, rels)
	local gb, grb, I, A ;
	gb:= GBNPGroebnerBasis( rels, kQ );
	I:= Ideal( kQ, gb );
	GroebnerBasis( I, gb );
	A:= kQ/I;
	return A;
end;


QuadraticDual:= function(KQ, Rels)		#Rels is a set of quadratic relations in the path algebra KQ. This fuction outputs the quadratic dual of KQ/(Rels)
	local gb, grb, PerpRels, kq, I, Aschrick ;
	PerpRels:= QuadraticPerpOfPathAlgebraIdeal( Rels );
	kq:= PerpRels[1];
	I:= Ideal( kq, PerpRels[2] );
	gb:= GroebnerBasisFunction( kq )( PerpRels[2], kq );
	grb:= GroebnerBasis( I, gb );
	Aschrick:= kq/I;
	AssignGeneratorVariables( Aschrick );
	return Aschrick;
end;


#################################################################################################################################################################################


LinearMapQPAtoGAP:= function(f)									#This function takes an algebra homomorphism f: M -> N in QPA and turns it into a linear map that GAP understands
	local Matf, LinMapf, NewSource, NewRange, BM, BN ;
	NewSource:= FullRowSpace( LeftActingDomain( Source( f ) ), Dimension( Source( f ) ) ) ;
	NewRange:= FullRowSpace( LeftActingDomain( Range( f ) ), Dimension( Range( f ) ) ) ;
	BM:= Basis( NewSource );
	BN:= Basis( NewRange );
	Matf:= MatricesOfPathAlgebraMatModuleHomomorphism( f );		#This method works because I am only considering quotients of path algebras over quivers with one vertex
	LinMapf:= LeftModuleHomomorphismByMatrix( BM, Matf[1], BN );
	return LinMapf ;
end;


HomSpace:= function(M, N)					#This function returns the vector space Hom_A(M,N), as a GAP object, for two (right) QPA A-modules M and N
	local BM, BN, FullHom, VectM, VectN, HomBasis, HomMNBasis, f, LinMapf, Matf, HomMN ;
	HomBasis:= HomOverAlgebra( M, N );
	BM:= Basis( M );
	BN:= Basis( N );
	HomMNBasis:= [ ];
	for f in HomBasis do									#Need to turn the QPA algebra homomorphisms into linear mappings that GAP sans QPA can understand
		LinMapf:= LinearMapQPAtoGAP( f );
		Add( HomMNBasis, LinMapf );
	od;
	HomMN:= VectorSpace( LeftActingDomain( M ), HomMNBasis, "basis" );
	return HomMN ;
end;


ContravariantHomAlgModFunctor:= function(f, A)				#inputs a module homomorphism f and a module A, outputs the map Hom( f, A )
	local HomDomain, HomRange, BRanGAP, Linf, x, CompMap, CompMapGAP, ImOfBasis, Homf ;
	if IsGeneralMapping( f ) = false then
		Print("The mapping is not linear or is not a mapping") ;
	elif not LeftActingDomain( A ) = LeftActingDomain( Source( f ) ) or not LeftActingDomain( A ) = LeftActingDomain( Range( f ) ) then ;
		Print("The vector spaces are not over the same field") ;
	else
		ImOfBasis:= [] ;
		HomDomain:= HomSpace( Source( f ), A );
		HomRange:= HomSpace( Range( f ), A );
		IsHandledByNiceBasis( HomDomain );
		IsHandledByNiceBasis( HomRange );
		BRanGAP:= Basis( HomRange );
		for x in BRanGAP do					   					#Sends a linear map g: Range( f ) -> A in the basis to the map gf: Source( f ) -> A
			Linf:= LinearMapQPAtoGAP( f );						#Turns the map f into a linear map GAP can work with
			Add( ImOfBasis, CompositionMapping( x, Linf ) ) ;
		od;
		Homf:= LeftModuleGeneralMappingByImages( HomRange, HomDomain, BRanGAP, ImOfBasis ) ;
		return Homf ;
	fi;
end;


CoHHomology:= function(A, n)		# Inputs an algebra A and a nonnegative integer n, outputs the Hochschild cohomology of A in degree n
	local M, ProjResA, dn, dn1, dnast, dn1ast, Ker, Im, Quotient ;
	M:= AlgebraAsModuleOverEnvelopingAlgebra( A );
	ProjResA:= ProjectiveResolution( M );
	dn:= DifferentialOfComplex( ProjResA, n );
	dn1:= DifferentialOfComplex( ProjResA, n+1 );
	dnast:= ContravariantHomAlgModFunctor( dn, M );
	dn1ast:= ContravariantHomAlgModFunctor( dn1, M );
	Ker:= KernelOfAdditiveGeneralMapping( dn1ast );
	Im:= Image( dnast );
	Quotient:= Ker/Im ;
	return Quotient ;
end;


CoHHomologyMaps:= function(A, n)
	local M, ProjResA, dn, dn1, dnast, dn1ast, L ;
	M:= AlgebraAsModuleOverEnvelopingAlgebra( A );
	ProjResA:= ProjectiveResolution( M );
	dn:= DifferentialOfComplex( ProjResA, n );
	dn1:= DifferentialOfComplex( ProjResA, n+1 );
	dnast:= ContravariantHomAlgModFunctor( dn, M );
	dn1ast:= ContravariantHomAlgModFunctor( dn1, M );
	L:= [ dn1ast, dnast ];
	return L ;
end;


#################################################################################################################################################################################


Example1:= function(K, a, b, c)
	local Q, kQ, rels, G, A ;
	Q:= Quiver( [ "e" ], [ [ "e", "e", "x1" ], [ "e", "e", "x2" ], [ "e", "e", "x3" ] ] );
	kQ:= PathAlgebra( K, Q );
	rels:= [ ( a )*kQ.x1*kQ.x2 + ( b )*kQ.x2*kQ.x1 + ( c )*kQ.x3^2, ( a )*kQ.x2*kQ.x3 + ( b )*kQ.x3*kQ.x2 + ( c )*kQ.x1^2, ( a )*kQ.x3*kQ.x1 + ( b )*kQ.x1*kQ.x3 + ( c )*kQ.x2^2 ] ;
	A:= GBQuotient( kQ, rels );
	return A;
end;
