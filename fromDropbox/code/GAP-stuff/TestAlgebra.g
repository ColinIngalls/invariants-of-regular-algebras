
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


FreeKAlgebraNoGeneratorNames:= function(K, n, indeterminate) 		#Constructs the free K-algebra on n generators as the path algbra of the n-rose
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



GBQuotient:= function(kQ, rels)
	local gb, grb, I, A ;
	gb:= GBNPGroebnerBasis( rels, kQ );
	I:= Ideal( kQ, gb );
	GroebnerBasis( I, gb );
	A:= kQ/I;
	return A;
end;



#Useful:= function(K)
#	local kQ, rels, A, M, ProjResA ;
#	kQ:= FreeKAlgebra( K, 2, "x" );
#	rels:= [ kQ.x1^2, kQ.x2^2, kQ.x1*kQ.x2 - kQ.x2*kQ.x1 ];
#	A:= kQ/rels;
#	M:= AlgebraAsModuleOverEnvelopingAlgebra( A );
#	ProjResA:= ProjectiveResolution( M );
#	return [ kQ, rels, A, M, ProjResA ];
#end;

#Useful2:= function(K)
#	local kQ, rels, A, M, ProjResA ;
#	kQ:= FreeKAlgebra( K, 3, "x" );
#	rels:= [ kQ.x1^2, kQ.x2^2, kQ.x3^2, kQ.x1*kQ.x2 - kQ.x2*kQ.x1, kQ.x1*kQ.x3 - kQ.x3*kQ.x1, kQ.x2*kQ.x3 - kQ.x3*kQ.x2 ];
#	A:= kQ/rels;
#	M:= AlgebraAsModuleOverEnvelopingAlgebra( A );
#	ProjResA:= ProjectiveResolution( M );
#	return [ kQ, rels, A, M, ProjResA ];
#end;


ExampleGeneratedByTwoElements:= function( K, q )
	local kQ, rels, A ;
	kQ:= FreeKAlgebra( K, 2, "x" );
	rels:= [ kQ.x2*kQ.x1 - q*kQ.x1*kQ.x2, kQ.x1^2, kQ.x2^2 ];
	A:= GBQuotient( kQ, rels );
	return [ A, kQ, rels ] ;
end;


ConvenientExample:= function( K, n )
	local kQ, rels, L, x, cart, A ;
	kQ:= FreeKAlgebra( K, n, "x" );
	L:= [ ] ; rels:= [ ];
	for x in GeneratorsOfAlgebra( kQ ) do
		if not x = One( kQ ) then
			Add( L, x );
		fi;
	od;
	cart:= Tuples( L, 2 );
	for x in cart do
		if x[1] = x[2] then
			Add( rels, x[1] * x[2] );
		else
			Add( rels, x[1]*x[2] - x[2]*x[1] );
		fi;
	od;
	A:= kQ/rels;
	return [ A, kQ, rels ] ;
end;


QuantumMatrices:= function( K, q ) #q is a nonzero element of the field K
	local kQ, rels, I, A ;
	kQ:= FreeKAlgebra( Rationals, 4, "x" );
	rels:= [];
	rels[1]:= kQ.x1*kQ.x2 - q*kQ.x2*kQ.x1 ;
	rels[2]:= kQ.x1*kQ.x3 - q*kQ.x3*kQ.x1 ;
	rels[3]:= kQ.x1*kQ.x4 - kQ.x4*kQ.x1 - ( q - Inverse( q ) )*kQ.x2*kQ.x3 ;
	rels[4]:= kQ.x2*kQ.x3 - kQ.x3*kQ.x2 ;
	rels[5]:= kQ.x2*kQ.x4 - q*kQ.x4*kQ.x2 ;
	rels[6]:= kQ.x3*kQ.x4 - q*kQ.x4*kQ.x3 ;
	A:= GBQuotient( kQ, rels );
	return [ A, kQ, rels ];
end;


NonKoszulExample:= function( K )
	local kQ, rels, A;
	kQ:= FreeKAlgebra( K, 2, "x" );
	rels:= [];
	rels[1]:= kQ.x1^2 ;
	rels[2]:= kQ.x2^2 - kQ.x1*kQ.x2 ;
	A:= GBQuotient( kQ, rels );
	return [ A, kQ, rels ];
end;


ExteriorAlgebra:= function( K, n )
	local kQ, rels, gens, cart, x, A ;
	kQ:= FreeKAlgebra( K, n, "x" );
	rels:= [];
	gens:= NonOneGeneratorsOfAlgebra( kQ );
	cart:= Cartesian( gens, gens );
	for x in cart do
		if x[1] = x[2] then
			Add( rels, x[1]*x[2] );
		else
			Add( rels, x[1]*x[2] + x[2]*x[1] );
		fi;
	od;
	A:= kQ/rels;
	return [ A, kQ, rels ];
end;


#################################################################################################################################################################################
#zhangzhang Algebras
#w = x1, x = x2, y = x3, z = x4


AlgebraA:= function( K )
	local kQ, rels, A, I, x1, x2, x3, x4;
	kQ:= FreeKAlgebraNoGeneratorNames( K, 4, "x" );
	rels:= [ ];
	rels[1]:= kQ.x1*kQ.x2 - kQ.x2*kQ.x1 ;
	rels[2]:= kQ.x4*kQ.x3 - kQ.x3*kQ.x4 - kQ.x3^2 ;
	rels[3]:= kQ.x3*kQ.x1 - kQ.x1*kQ.x3 ;
	rels[4]:= kQ.x2*kQ.x3 + kQ.x1*kQ.x4 - kQ.x3*kQ.x2 ;
	rels[5]:= kQ.x4*kQ.x1 - kQ.x1*kQ.x4 ;
	rels[6]:= kQ.x4*kQ.x2 + (2)*kQ.x2*kQ.x3 + kQ.x1*kQ.x4 - kQ.x2*kQ.x4 ;
	A:= GBQuotient( kQ, rels );
	return [ A, kQ, rels ];
end;

AlgebraA2:= function( K, h )
	local kQ, rels, A, I, x1, x2, x3, x4;
	kQ:= FreeKAlgebraNoGeneratorNames( K, 4, "x" );
	rels:= [ ];
	rels[1]:= h*(kQ.x1*kQ.x2 - kQ.x2*kQ.x1) ;
	rels[2]:= h*(kQ.x4*kQ.x3 - kQ.x3*kQ.x4 - kQ.x3^2) ;
	rels[3]:= h*(kQ.x3*kQ.x1 - kQ.x1*kQ.x3) ;
	rels[4]:= h*(kQ.x2*kQ.x3 + kQ.x1*kQ.x4 - kQ.x3*kQ.x2) ;
	rels[5]:= h*(kQ.x4*kQ.x1 - kQ.x1*kQ.x4) ;
	rels[6]:= h*(kQ.x4*kQ.x2 + (2)*kQ.x2*kQ.x3 + kQ.x1*kQ.x4 - kQ.x2*kQ.x4) ;
	A:= GBQuotient( kQ, rels );
	return [ A, kQ, rels ];
end;

AlgebraB:= function() #Need p^2 = -1 in K. For instance, K = Z_101 and p = 10
	local kQ, p, rels, B, x1, x2, x3, x4;
	kQ:= FreeKAlgebraNoGeneratorNames( GF(101), 4, "x" );
	p:= 10*One(GF(101));
	rels:= [];
	rels[1]:= kQ.x2*kQ.x1 - p*kQ.x1*kQ.x2 ;
	rels[2]:= kQ.x4*kQ.x3 - p*kQ.x3*kQ.x4 ;
#
	rels[3]:= kQ.x3*kQ.x1 - kQ.x2*kQ.x4 ;
	rels[4]:= kQ.x3*kQ.x2 - kQ.x1*kQ.x4 ;
	rels[5]:= kQ.x4*kQ.x1 + kQ.x2*kQ.x3 ;
	rels[6]:= kQ.x4*kQ.x2 - kQ.x1*kQ.x3 ;
	B:= GBQuotient( kQ, rels );
	return [ B, kQ, rels ];
end;


AlgebraB2:= function() #Need p^2 = -1 in K. For instance, K = Z_101 and p = 10
	local kQ, p, rels, B, x1, x2, x3, x4;
	kQ:= FreeKAlgebraNoGeneratorNames( GaussianRationals, 4, "x" );
	p:= E(4);
	rels:= [];
	rels[1]:= kQ.x2*kQ.x1 - p*kQ.x1*kQ.x2 ;
	rels[2]:= kQ.x4*kQ.x3 - p*kQ.x3*kQ.x4 ;
#
	rels[3]:= kQ.x3*kQ.x1 - kQ.x2*kQ.x4 ;
	rels[4]:= kQ.x3*kQ.x2 - kQ.x1*kQ.x4 ;
	rels[5]:= kQ.x4*kQ.x1 + kQ.x2*kQ.x3 ;
	rels[6]:= kQ.x4*kQ.x2 - kQ.x1*kQ.x3 ;
	B:= GBQuotient( kQ, rels );
	return [ B, kQ, rels ];
end;


AlgebraC:= function() #p^2 + p + 1 = 0, for instance, K = Z_601 and p = 24 # E()
	local kQ, p, rels, C, x1, x2, x3, x4;
	kQ:= FreeKAlgebraNoGeneratorNames( GF(601), 4, "x" );
	p:= 24*One(GF(601));
	rels:= [];
	rels[1]:= kQ.x4*kQ.x3 - p*kQ.x3*kQ.x4 ;
	rels[2]:= kQ.x2*kQ.x1 - p*kQ.x1*kQ.x2 ;
#
	rels[3]:= kQ.x3*kQ.x1 + kQ.x1*kQ.x3 - (p^2)*kQ.x2*kQ.x3 - kQ.x1*kQ.x4 + p*kQ.x2*kQ.x4 ;
	rels[4]:= kQ.x3*kQ.x2 + p*kQ.x1*kQ.x3 - kQ.x2*kQ.x3 - kQ.x1*kQ.x4 + p*kQ.x2*kQ.x4 ;
	rels[5]:= kQ.x4*kQ.x1 + p*kQ.x1*kQ.x3 + 2*(p^2)*kQ.x2*kQ.x3 - p*kQ.x1*kQ.x4 + p*kQ.x2*kQ.x4 ;
	rels[6]:= kQ.x4*kQ.x2 + p*kQ.x1*kQ.x3 - (p^2)*kQ.x2*kQ.x3 - kQ.x1*kQ.x4 + kQ.x2*kQ.x4 ;
	C:= GBQuotient( kQ, rels );
	return [ C, kQ, rels ];
end;


AlgebraC2:= function() #p^2 + p + 1 = 0, for instance, K = Z_601 and p = 24
	local t, poly, Qadj, kQ, p, rels, C, x1, x2, x3, x4;
	Qadj:= CF(Rationals, 3);
	p:= E(3);
	kQ:= FreeKAlgebraNoGeneratorNames( Qadj, 4, "x" );
	rels:= [];
	rels[1]:= kQ.x4*kQ.x3 - p*kQ.x3*kQ.x4 ;
	rels[2]:= kQ.x2*kQ.x1 - p*kQ.x1*kQ.x2 ;
#
	rels[3]:= kQ.x3*kQ.x1 + kQ.x1*kQ.x3 - (p^2)*kQ.x2*kQ.x3 - kQ.x1*kQ.x4 + p*kQ.x2*kQ.x4 ;
	rels[4]:= kQ.x3*kQ.x2 + p*kQ.x1*kQ.x3 - kQ.x2*kQ.x3 - kQ.x1*kQ.x4 + p*kQ.x2*kQ.x4 ;
	rels[5]:= kQ.x4*kQ.x1 + p*kQ.x1*kQ.x3 + 2*(p^2)*kQ.x2*kQ.x3 - p*kQ.x1*kQ.x4 + p*kQ.x2*kQ.x4 ;
	rels[6]:= kQ.x4*kQ.x2 + p*kQ.x1*kQ.x3 - (p^2)*kQ.x2*kQ.x3 - kQ.x1*kQ.x4 + kQ.x2*kQ.x4 ;
	C:= GBQuotient( kQ, rels );
	return [ C, kQ, rels ];
end;


#AlgebraC2:= function() #p^2 + p + 1 = 0, for instance, K = Z_601 and p = 24
#	local t, poly, Qadj, kQ, p, rels, C, x1, x2, x3, x4;
#	t:= X( Rationals, "t" );
#	poly:= t^2 + t + 1;
#	Qadj:= AlgebraicExtension( Rationals, poly, "p" );
#	p:= RootOfDefiningPolynomial( Qadj );
#	kQ:= FreeKAlgebraNoGeneratorNames( Qadj, 4, "x" );
#	rels:= [];
#	rels[1]:= kQ.x4*kQ.x3 - p*kQ.x3*kQ.x4 ;
#	rels[2]:= kQ.x2*kQ.x1 - p*kQ.x1*kQ.x2 ;
#
#	rels[3]:= kQ.x3*kQ.x1 + kQ.x1*kQ.x3 - (p^2)*kQ.x2*kQ.x3 - kQ.x1*kQ.x4 + p*kQ.x2*kQ.x4 ;
#	rels[4]:= kQ.x3*kQ.x2 + p*kQ.x1*kQ.x3 - kQ.x2*kQ.x3 - kQ.x1*kQ.x4 + p*kQ.x2*kQ.x4 ;
#	rels[5]:= kQ.x4*kQ.x1 + p*kQ.x1*kQ.x3 + 2*(p^2)*kQ.x2*kQ.x3 - p*kQ.x1*kQ.x4 + p*kQ.x2*kQ.x4 ;
#	rels[6]:= kQ.x4*kQ.x2 + p*kQ.x1*kQ.x3 - (p^2)*kQ.x2*kQ.x3 - kQ.x1*kQ.x4 + kQ.x2*kQ.x4 ;
#	C:= GBQuotient( kQ, rels );
#	return [ C, kQ, rels ];
#end;


AlgebraD:= function( K, p )
	local kQ, rels, D, x1, x2, x3, x4;
	if p = 1 or p = -1 then
		kQ:= FreeKAlgebraNoGeneratorNames( K, 4, "x" );
		rels:= [];
		rels[1]:= kQ.x1*kQ.x2 + kQ.x2*kQ.x1 ;
		rels[2]:= kQ.x4*kQ.x3 - p*kQ.x3*kQ.x4 ;
#
		rels[3]:= kQ.x3*kQ.x1 + p*kQ.x1*kQ.x3 ;
		rels[4]:= kQ.x3*kQ.x2 + (p*p)*kQ.x2*kQ.x3 - kQ.x1*kQ.x4 ;
		rels[5]:= kQ.x4*kQ.x1 - p*kQ.x1*kQ.x4 ;
		rels[6]:= kQ.x4*kQ.x2 - kQ.x1*kQ.x3 - kQ.x2*kQ.x4 ;
		D:= GBQuotient( kQ, rels );
		return [ D, kQ, rels ];
	else
		Print("p must be either 1 or -1");
	fi;
end;


AlgebraE:= function( )
	local kQ, p, rels, Ee, x1, x2, x3, x4;
	kQ:= FreeKAlgebraNoGeneratorNames( GaussianRationals, 4, "x" );
	p:= E(4);
	rels:= [];
	rels[1]:= kQ.x2*kQ.x1 + kQ.x1*kQ.x2 ;
	rels[2]:= kQ.x4*kQ.x3 - p*kQ.x3*kQ.x4 ;
#
	rels[3]:= kQ.x3*kQ.x1 - kQ.x1*kQ.x4 - kQ.x2*kQ.x4 ;
	rels[4]:= kQ.x3*kQ.x2 - kQ.x1*kQ.x4 + kQ.x2*kQ.x4 ;
	rels[5]:= kQ.x4*kQ.x1 + kQ.x1*kQ.x3 - kQ.x2*kQ.x3 ;
	rels[6]:= kQ.x4*kQ.x2 - kQ.x1*kQ.x3 - kQ.x2*kQ.x3 ;
	Ee:= GBQuotient( kQ, rels );
	return [ Ee, kQ, rels ];
end;


AlgebraF:= function( )
	local kQ, p, rels, F, x1, x2, x3, x4;
	kQ:= FreeKAlgebraNoGeneratorNames( GaussianRationals, 4, "x" );
	p:= E(4);
	rels:= [ ];
	rels[1]:= kQ.x2*kQ.x1 + kQ.x1*kQ.x2 ;
	rels[2]:= kQ.x4*kQ.x3 - p*kQ.x3*kQ.x4 ;
#
	rels[3]:= kQ.x3*kQ.x1 + kQ.x1*kQ.x3 + p*kQ.x2*kQ.x3 - kQ.x1*kQ.x4 + kQ.x2*kQ.x4 ;
	rels[4]:= kQ.x3*kQ.x2 + p*kQ.x1*kQ.x3 - kQ.x2*kQ.x3 - kQ.x1*kQ.x4 - kQ.x2*kQ.x4 ;
	rels[5]:= kQ.x4*kQ.x1 + p*kQ.x1*kQ.x3 - p*kQ.x2*kQ.x3 - p*kQ.x1*kQ.x4 - kQ.x2*kQ.x4 ;
	rels[6]:= kQ.x4*kQ.x2 + p*kQ.x1*kQ.x3 + p*kQ.x2*kQ.x3 - kQ.x1*kQ.x4 + p*kQ.x2*kQ.x4 ;
	F:= GBQuotient( kQ, rels );
	return [ F, kQ, rels ];
end;


AlgebraG:= function( K, p, f )
	local kQ, rels, G, x1, x2, x3, x4;
	kQ:= FreeKAlgebraNoGeneratorNames( K, 4, "x" );
	rels:= [];
	if f = Zero( kQ ) then
		Error( "f needs to be nonzero" );
	else
		rels[1]:= kQ.x2*kQ.x1 - kQ.x1*kQ.x2 ;
		rels[2]:= kQ.x4*kQ.x3 - p*kQ.x3*kQ.x4 ;
#
		rels[3]:= kQ.x3*kQ.x1 - p*kQ.x1*kQ.x3 ;
		rels[4]:= kQ.x3*kQ.x2 - p*kQ.x1*kQ.x3 - (p*p)*kQ.x2*kQ.x3 - kQ.x1*kQ.x4;
		rels[5]:= kQ.x4*kQ.x1 - p*kQ.x1*kQ.x4 ;
		rels[6]:= kQ.x4*kQ.x2 - f*kQ.x1*kQ.x3 + kQ.x1*kQ.x4 - kQ.x2*kQ.x4;
		G:= GBQuotient( kQ, rels );
		return [G, kQ, rels] ;
	fi;
end;



AlgebraH:= function( K, p, f )
	local kQ, rels, G, x1, x2, x3, x4;
	kQ:= FreeKAlgebraNoGeneratorNames( K, 4, "x" );
	rels:= [];
end;


AlgebraI:= function( )   #Need to find a way to encode q^2 = -1 # Use the function FieldExtension
	local kQ, rels, q, I, J, x1, x2, x3, x4;
	kQ:= FreeKAlgebraNoGeneratorNames( GaussianRationals, 4, "x" );
	q:= E(4);
	rels:= [ ];
	rels[1]:= kQ.x2*kQ.x1 - q*kQ.x1*kQ.x2 ;
	rels[2]:= kQ.x4*kQ.x3 + kQ.x3*kQ.x4 ;
	rels[3]:= kQ.x3*kQ.x1 + q*kQ.x1*kQ.x3 + q*kQ.x2*kQ.x3 - kQ.x1*kQ.x4 + q*kQ.x2*kQ.x4 ;
	rels[4]:= kQ.x3*kQ.x2 - kQ.x1*kQ.x3 - kQ.x2*kQ.x3 - kQ.x1*kQ.x4 + q*kQ.x2*kQ.x4 ;
	rels[5]:= kQ.x4*kQ.x1 - kQ.x1*kQ.x3 - q*kQ.x2*kQ.x3 - q*kQ.x1*kQ.x4 + q*kQ.x2*kQ.x4 ;
	rels[6]:= kQ.x4*kQ.x2 + kQ.x1*kQ.x3 + q*kQ.x2*kQ.x3 - kQ.x1 * kQ.x4 + kQ.x2*kQ.x4 ;
#	J:= Ideal( kQ, rels );
	I:= GBQuotient( kQ, rels );
	return [I, kQ, rels ];
end;


AlgebraJ:= function( )
	local kQ, rels, q, J, x1, x2, x3, x4;
	kQ:= FreeKAlgebraNoGeneratorNames( GaussianRationals, 4, "x" );
	q:= E(4);
	rels:= [];
	rels[1]:= kQ.x2*kQ.x1 - q*kQ.x1*kQ.x2 ;
	rels[2]:= kQ.x4*kQ.x3 + kQ.x3*kQ.x4 ;
#
	rels[3]:= kQ.x3*kQ.x1 - kQ.x2*kQ.x3 - kQ.x2*kQ.x4 ;
	rels[4]:= kQ.x3*kQ.x2 + kQ.x1*kQ.x3 - kQ.x1*kQ.x4 ;
	rels[5]:= kQ.x4*kQ.x1 - kQ.x2*kQ.x3 + kQ.x2*kQ.x4 ;
	rels[6]:= kQ.x4*kQ.x2 - kQ.x1*kQ.x3 - kQ.x1*kQ.x4 ;
	J:= GBQuotient( kQ, rels );
	return [ J, kQ, rels ];
end;


AlgebraK:= function( K, q, f ) #q = 1 or q = -1
	local kQ, rels, KAlg, x1, x2, x3, x4;
	kQ:= FreeKAlgebraNoGeneratorNames( K, 4, "x" );
	rels:= [];
	if f = Zero( K ) then
		Error("f needs to be nonzero, and q can only be 1 or -1");
	else
		rels[1]:= kQ.x2*kQ.x1 - q*kQ.x1*kQ.x2 ;
		rels[2]:= kQ.x4*kQ.x3 + kQ.x3*kQ.x4 ;
#
		rels[3]:= kQ.x3*kQ.x1 - kQ.x1*kQ.x3 ;
		rels[4]:= kQ.x3*kQ.x2 - kQ.x2*kQ.x4 ;
		rels[5]:= kQ.x4*kQ.x1 - kQ.x1*kQ.x4 ;
		rels[6]:= kQ.x4*kQ.x2 - f*kQ.x2*kQ.x3 ;
		KAlg:= GBQuotient( kQ, rels );
		return [ KAlg, kQ, rels ];
	fi;
end;


AlgebraL:= function( K, q, f ) #q = 1 or q = -1
	local kQ, rels, L, x1, x2, x3, x4;
	kQ:= FreeKAlgebraNoGeneratorNames( K, 4, "x" );
	rels:= [];
	if f = Zero( K ) then
		Error("f needs to be nonzero, and q can only be 1 or -1");
	else
		rels[1]:= kQ.x2*kQ.x1 - q*kQ.x1*kQ.x2 ;
		rels[2]:= kQ.x4*kQ.x3 + kQ.x3*kQ.x4 ;
#
		rels[3]:= kQ.x3*kQ.x1 - f*kQ.x1*kQ.x4 ;
		rels[4]:= kQ.x3*kQ.x2 - kQ.x2*kQ.x4 ;
		rels[5]:= kQ.x4*kQ.x1 - f*kQ.x1*kQ.x3 ;
		rels[6]:= kQ.x4*kQ.x2 - kQ.x2*kQ.x3 ;
		L:= GBQuotient( kQ, rels );
		return [ L, kQ, rels ];
	fi;
end;


AlgebraM:= function( K, f )
	local kQ, rels, M, x1, x2, x3, x4;
	kQ:= FreeKAlgebraNoGeneratorNames( K, 4, "x" );
	if f = One( K ) then
		return "f cannot be 1";
	else
		rels:= [];
		rels[1]:= kQ.x2*kQ.x1 + kQ.x1*kQ.x2 ;
		rels[2]:= kQ.x4*kQ.x3 + kQ.x3*kQ.x4 ;
#
		rels[3]:= kQ.x3*kQ.x1 - kQ.x2*kQ.x3 - kQ.x1*kQ.x4 ;
		rels[4]:= kQ.x3*kQ.x2 - f*kQ.x1*kQ.x3 + kQ.x2*kQ.x4 ;
		rels[5]:= kQ.x4*kQ.x1 - kQ.x1*kQ.x3 + kQ.x2*kQ.x4 ;
		rels[6]:= kQ.x4*kQ.x2 + kQ.x2*kQ.x3 + f*kQ.x1*kQ.x4 ;
		M:= GBQuotient( kQ, rels );
		return [ M, kQ, rels ];
	fi;
end;


AlgebraN:= function( K, f, g )
	local kQ, rels, N, x1, x2, x3, x4;
	kQ:= FreeKAlgebraNoGeneratorNames( K, 4, "x" );
	if f^2 = g^2 then
		return "f^2 cannot equal g^2";
	else
		rels:= [];
		rels[1]:= kQ.x2*kQ.x1 + kQ.x1*kQ.x2 ;
		rels[2]:= kQ.x4*kQ.x3 + kQ.x3*kQ.x4 ;
#
		rels[3]:= kQ.x3*kQ.x1 + g*kQ.x2*kQ.x3 - f*kQ.x2*kQ.x4 ;
		rels[4]:= kQ.x3*kQ.x2 - g*kQ.x1*kQ.x3 - f*kQ.x1*kQ.x4 ;
		rels[5]:= kQ.x4*kQ.x1 - f*kQ.x2*kQ.x3 + g*kQ.x2*kQ.x4 ;
		rels[6]:= kQ.x4*kQ.x2 - f*kQ.x1*kQ.x3 - g*kQ.x1*kQ.x4 ;
		N:= GBQuotient( kQ, rels );
		return [ N, kQ, rels ];
	fi;
end;


AlgebraO:= function( K, f )
	local kQ, rels, I, O, x1, x2, x3, x4;
	kQ:= FreeKAlgebraNoGeneratorNames( K, 4, "x" );
	if f = One( K ) then
		return "f cannot be 1";
	else
		rels:= [ ];
		rels[1]:= kQ.x2*kQ.x1 + kQ.x1*kQ.x2 ;
		rels[2]:= kQ.x4*kQ.x3 + kQ.x3*kQ.x4 ;
#
		rels[3]:= kQ.x3*kQ.x1 - kQ.x1*kQ.x3 - f*kQ.x2*kQ.x4 ;
		rels[4]:= kQ.x3*kQ.x2 + kQ.x2*kQ.x3 - kQ.x1*kQ.x4 ;
		rels[5]:= kQ.x4*kQ.x1 - f*kQ.x2*kQ.x3 + kQ.x1*kQ.x4 ;
		rels[6]:= kQ.x4*kQ.x2 - kQ.x1*kQ.x3 - kQ.x2*kQ.x4 ;
		O:= GBQuotient( kQ, rels );
		return [ O, kQ, rels ];
	fi;
end;


AlgebraP:= function( K, f ) #Check for f = 0
	local kQ, rels, I, Palg, x1, x2, x3, x4;
	kQ:= FreeKAlgebraNoGeneratorNames( K, 4, "x" );
	if f = One( K ) then
		return "f cannot be 1";
	else
		rels:= [ ];
		rels[1]:= kQ.x2*kQ.x1 + kQ.x1*kQ.x2 ;
		rels[2]:= kQ.x4*kQ.x3 + kQ.x3*kQ.x4 ;
#
		rels[3]:= kQ.x3*kQ.x1 - kQ.x1*kQ.x4 - f*kQ.x2*kQ.x4 ;
		rels[4]:= kQ.x3*kQ.x2 - kQ.x1*kQ.x4 - kQ.x2*kQ.x4 ;
		rels[5]:= kQ.x4*kQ.x1 - kQ.x1*kQ.x3 + f*kQ.x2*kQ.x3 ;
		rels[6]:= kQ.x4*kQ.x2 + kQ.x1*kQ.x3 - kQ.x2*kQ.x3 ;
		Palg:= GBQuotient( kQ, rels );
		return [ Palg, kQ, rels ];
	fi;
end;


AlgebraQ:= function( K )
	local kQ, rels, I, Q, x1, x2, x3, x4;
	kQ:= FreeKAlgebraNoGeneratorNames( K, 4, "x" );
	rels:= [ ];
	rels[1]:= kQ.x2*kQ.x1 + kQ.x1*kQ.x2 ;
	rels[2]:= kQ.x4*kQ.x3 + kQ.x3*kQ.x4 ;
#
	rels[3]:= kQ.x3*kQ.x1 - kQ.x1*kQ.x4 ;
	rels[4]:= kQ.x3*kQ.x2 - kQ.x1*kQ.x3 - kQ.x2*kQ.x3 - kQ.x1*kQ.x4 ;
	rels[5]:= kQ.x4*kQ.x1 + kQ.x1*kQ.x3 ;
	rels[6]:= kQ.x4*kQ.x2 - kQ.x1*kQ.x3 + kQ.x1*kQ.x4 - kQ.x2*kQ.x4 ;
	Q:= GBQuotient( kQ, rels );
	return [ Q, kQ, rels ];
end;


AlgebraR:= function( K )
	local kQ, rels, I, R, x1, x2, x3, x4;
	kQ:= FreeKAlgebraNoGeneratorNames( K, 4, "x" );
	rels:= [ ];
	rels[1]:= kQ.x2*kQ.x1 + kQ.x1*kQ.x2 ;
	rels[2]:= kQ.x4*kQ.x3 + kQ.x3*kQ.x4 ;
#
	rels[3]:= kQ.x3*kQ.x1 - kQ.x1*kQ.x3 - kQ.x2*kQ.x3 - kQ.x1*kQ.x4 ;
	rels[4]:= kQ.x3*kQ.x2 - kQ.x1*kQ.x4 ;
	rels[5]:= kQ.x4*kQ.x1 - kQ.x2*kQ.x3 ;
	rels[6]:= kQ.x4*kQ.x2 + kQ.x2*kQ.x3 + kQ.x1*kQ.x4 - kQ.x2*kQ.x4 ;
	R:= GBQuotient( kQ, rels );
	return [ R, kQ, rels ];
end;


AlgebraS:= function( K )
	local kQ, rels, S, x1, x2, x3, x4;
	kQ:= FreeKAlgebraNoGeneratorNames( K, 4, "x" );
end;


AlgebraT:= function( K )
	local kQ, rels, I, T, x1, x2, x3, x4;
	kQ:= FreeKAlgebraNoGeneratorNames( K, 4, "x" );
	rels:= [];
	rels[1]:= kQ.x2*kQ.x1 + kQ.x1*kQ.x2 ;
	rels[2]:= kQ.x4*kQ.x3 + kQ.x3*kQ.x4 ;
#
	rels[3]:= kQ.x3*kQ.x1 + kQ.x1*kQ.x3 - kQ.x2*kQ.x3 - kQ.x1*kQ.x4 - kQ.x2*kQ.x4 ;
	rels[4]:= kQ.x3*kQ.x2 - kQ.x1*kQ.x3 + kQ.x2*kQ.x3 - kQ.x1*kQ.x4 - kQ.x2*kQ.x4 ;
	rels[5]:= kQ.x4*kQ.x1 - kQ.x1*kQ.x3 - kQ.x2*kQ.x3 - kQ.x1*kQ.x4 + kQ.x2*kQ.x4 ;
	rels[6]:= kQ.x4*kQ.x2 - kQ.x1*kQ.x3 - kQ.x2*kQ.x3 + kQ.x1*kQ.x4 - kQ.x2*kQ.x4 ;
	T:= GBQuotient( kQ, rels );
	return [ T, kQ, rels ];
end;


AlgebraU:= function( K )
	local kQ, rels, U, x1, x2, x3, x4;
	kQ:= FreeKAlgebraNoGeneratorNames( K, 4, "x" );
end;


AlgebraV:= function( K )
	local kQ, rels, V, x1, x2, x3, x4;
	kQ:= FreeKAlgebraNoGeneratorNames( K, 4, "x" );
end;


AlgebraW:= function( K )
	local kQ, rels, W, x1, x2, x3, x4;
	kQ:= FreeKAlgebraNoGeneratorNames( K, 4, "x" );
end;


AlgebraX:= function( K )
	local kQ, rels, X, x1, x2, x3, x4;
	kQ:= FreeKAlgebraNoGeneratorNames( K, 4, "x" );
end;


AlgebraY:= function( K )
	local kQ, rels, Y, x1, x2, x3, x4;
	kQ:= FreeKAlgebraNoGeneratorNames( K, 4, "x" );
end;


AlgebraZ:= function( K, f ) #need f(f+1) != 0
	local kQ, rels, I, Zalg, x1, x2, x3, x4;
	kQ:= FreeKAlgebraNoGeneratorNames( K, 4, "x" );
#	if f*(1+f) = 0 then
#		Print( "Need f(1+f) != 0" );
#	else
		rels:= [ ];
		rels[1]:= kQ.x1*kQ.x2 + kQ.x2*kQ.x1 ;
		rels[2]:= kQ.x4*kQ.x3 - kQ.x3*kQ.x4 ;
		rels[3]:= kQ.x3*kQ.x1 - kQ.x1*kQ.x4 - kQ.x2*kQ.x4 ;
		rels[4]:= kQ.x3*kQ.x2 - kQ.x2*kQ.x3 - kQ.x1*kQ.x4 ;
		rels[5]:= kQ.x4*kQ.x1 - f*kQ.x2*kQ.x3 + kQ.x1*kQ.x4 ;
		rels[6]:= kQ.x4*kQ.x2 - f*kQ.x1*kQ.x4 + kQ.x2*kQ.x4 ;
		I:= Ideal( kQ, rels );
#		Zalg:= GBQuotient( kQ, rels );
#		Zalg:= kQ/I ;
		return [ 0, kQ, rels ];
#	fi;
end;


#################################################################################################################################################################################


LeBruynAlgebra:= function( K, a, b, c, alphalist, SymMat )	# alphalist is a list [ alpha1, alpha2, alpha3 ]
																													# of lists of elements of k, and SymMay is a list
																													# of lists of elements of k representing a symmetric
																													# 3x3 matrix. Also, we set x4 = z
	local kQ, rels, A, I, gb, x1, x2, x3, x4 ;
	kQ:= FreeKAlgebra( K, 4, "x" );
	rels:=[];
	rels[1]:= c*kQ.x1^2 + a*kQ.x2*kQ.x3 + b*kQ.x3*kQ.x2 + SymMat[1][1]*kQ.x1*kQ.x4 + SymMat[1][2]*kQ.x2*kQ.x4 + SymMat[1][3]*kQ.x3*kQ.x4 + alphalist[1]*kQ.x4^2 ;
	rels[2]:= c*kQ.x2^2 + a*kQ.x3*kQ.x1 + b*kQ.x1*kQ.x3 + SymMat[2][1]*kQ.x1*kQ.x4 + SymMat[2][2]*kQ.x2*kQ.x4 + SymMat[2][3]*kQ.x3*kQ.x4 + alphalist[2]*kQ.x4^2 ;
	rels[3]:= c*kQ.x3^2 + a*kQ.x1*kQ.x2 + b*kQ.x2*kQ.x1 + SymMat[3][1]*kQ.x1*kQ.x4 + SymMat[3][2]*kQ.x2*kQ.x4 + SymMat[3][3]*kQ.x3*kQ.x4 + alphalist[3]*kQ.x4^2 ;
	rels[4]:= kQ.x1*kQ.x4 - kQ.x4*kQ.x1 ;
	rels[5]:= kQ.x2*kQ.x4 - kQ.x4*kQ.x2 ;
	rels[6]:= kQ.x3*kQ.x4 - kQ.x4*kQ.x3 ;
#	I:= Ideal( kQ, rels );
#	gb:= GroebnerBasis( I, rels );
#	A:= kQ/I ;
	A:= GBQuotient( kQ, rels );
	return [ A, kQ, rels ] ;
end;


LeBruynAlgebra2:= function( K, a, b, c )	#a, b, c are elements of k
	local kQ, rels, A, I, gb, x1, x2, x3, x4 ;
	kQ:= FreeKAlgebra( K, 3, "x" );
	rels:=[];
	rels[1]:= c*kQ.x1^2 + a*kQ.x2*kQ.x3 + b*kQ.x3*kQ.x2 ;
	rels[2]:= c*kQ.x2^2 + a*kQ.x3*kQ.x1 + b*kQ.x1*kQ.x3 ;
	rels[3]:= c*kQ.x3^2 + a*kQ.x1*kQ.x2 + b*kQ.x2*kQ.x1 ;
#	I:= Ideal( kQ, rels );
#	gb:= GroebnerBasis( I, rels );
#	A:= kQ/I ;
#	A:= GBQuotient( kQ, rels );
	return [ 0, kQ, rels ] ;
end;


#################################################################################################################################################################################

#These algebras are sources from cocycle-twists.pdf

Commutator:= function( x, y )
	return LieBracket( x, y );
end;

SkewCommutator:= function( x, y )
	return x*y + y*x ;
end;


4dSklyaninAlgebra:= function( K, beta, gamma )
	local kQ, alpha, rels, I, gb, A ;
	alpha:= -(beta + gamma)/(1 + beta*gamma) ;
	kQ:= FreeKAlgebra( K, 4, "x" );
	rels:= [ ];
	rels[1]:= Commutator( kQ.x1, kQ.x2 ) - alpha*SkewCommutator( kQ.x3, kQ.x4 ) ;
	rels[2]:= SkewCommutator( kQ.x1, kQ.x2 ) - Commutator( kQ.x3, kQ.x4 ) ;
	rels[3]:= Commutator( kQ.x1, kQ.x3 ) - beta*SkewCommutator( kQ.x4, kQ.x2 );
	rels[4]:= SkewCommutator( kQ.x1, kQ.x3 ) - Commutator( kQ.x4, kQ.x2 );
	rels[5]:= Commutator( kQ.x1, kQ.x4 ) - gamma*SkewCommutator( kQ.x2, kQ.x3 ) ;
	rels[6]:= SkewCommutator( kQ.x1, kQ.x4 ) - Commutator( kQ.x2, kQ.x3 );
	I:= Ideal( kQ, rels );
	gb:= GroebnerBasis( I, rels );
	A:= kQ/I ;
#	A:= GBQuotient( kQ, rels );
	return [ A, kQ, rels ];
end;
