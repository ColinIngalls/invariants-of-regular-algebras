
LoadPackage("qpa");


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


FreeCommutativeAlgebra:= function( K, n )
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
#x1 = x1, x2 = x2, x3 = y1, x4 = y2

AlgebraA:= function( K, h )
	local kQ, rels, A, I, x1, x2, x3, x4;
	kQ:= FreeKAlgebraNoGeneratorNames( K, 4, "x" );
	rels:= [ ];
	rels[1]:= kQ.x1*kQ.x2 - kQ.x2*kQ.x1 ;
	rels[2]:= kQ.x4*kQ.x3 - kQ.x3*kQ.x4 - kQ.x3^2 ;
  #zy - yz - y^2
	rels[3]:= kQ.x3*kQ.x1 - h*kQ.x1*kQ.x3 ;
	rels[4]:= kQ.x3*kQ.x2 - h*(kQ.x1*kQ.x4 + kQ.x2*kQ.x3) ;
	rels[5]:= kQ.x4*kQ.x1 - h*kQ.x1*kQ.x4 ;
	rels[6]:= kQ.x4*kQ.x2 + h*((2)*kQ.x2*kQ.x3 + kQ.x1*kQ.x4 - kQ.x2*kQ.x4) ;
#	A:= GBQuotient( kQ, rels );
	return [ 0, kQ, rels ];
end;



AlgebraB:= function( h ) #Need p^2 = -1 in K. For instance, K = Z_101 and p = 10
	local kQ, p, rels, B, x1, x2, x3, x4;
	kQ:= FreeKAlgebraNoGeneratorNames( GaussianRationals, 4, "x" );
	p:= E(4);
	rels:= [];
	#xw - wx
	rels[1]:= kQ.x2*kQ.x1 - p*kQ.x1*kQ.x2 ;
	
	#zy - pyz
	rels[2]:= kQ.x4*kQ.x3 - p*kQ.x3*kQ.x4 ;

	#yw - xz
	rels[3]:= kQ.x3*kQ.x1 + h*(-kQ.x2*kQ.x4) ;

	#yx - wz
	rels[4]:= kQ.x3*kQ.x2 + h*(-kQ.x1*kQ.x4) ;

	#zw + xy
	rels[5]:= kQ.x4*kQ.x1 + h*(kQ.x2*kQ.x3) ;

	#zx - wy
	rels[6]:= kQ.x4*kQ.x2 + h*(-kQ.x1*kQ.x3) ;
	B:= GBQuotient( kQ, rels );
	return [ B, kQ, rels ];
end;



AlgebraC:= function( h ) #p^2 + p + 1 = 0, for instance, K = Z_601 and p = 24
	local t, poly, Qadj, kQ, p, rels, C, x1, x2, x3, x4;
	Qadj:= CF(Rationals, 3);
	p:= E(3);
	kQ:= FreeKAlgebraNoGeneratorNames( Qadj, 4, "x" );
	rels:= [];

	#zy - pyz
	rels[1]:= kQ.x4*kQ.x3 - p*kQ.x3*kQ.x4 ;
	
	#xw - pwx
	rels[2]:= kQ.x2*kQ.x1 - p*kQ.x1*kQ.x2 ;

	#yw + wy - p^2xy - wz + pxz
	rels[3]:= kQ.x3*kQ.x1 + h*(kQ.x1*kQ.x3 - (p^2)*kQ.x2*kQ.x3 - kQ.x1*kQ.x4 + p*kQ.x2*kQ.x4) ;
	
	#yx + pwy - xy - wz + pxz
	rels[4]:= kQ.x3*kQ.x2 + h*(p*kQ.x1*kQ.x3 - kQ.x2*kQ.x3 - kQ.x1*kQ.x4 + p*kQ.x2*kQ.x4) ;
	
	#zw + pwy + 2p^2xy - pwz + pxz
	rels[5]:= kQ.x4*kQ.x1 + h*(p*kQ.x1*kQ.x3 + 2*(p^2)*kQ.x2*kQ.x3 - p*kQ.x1*kQ.x4 + p*kQ.x2*kQ.x4) ;
	
	#zx + pwy - p^2xy - wz + xz
	rels[6]:= kQ.x4*kQ.x2 + h*(p*kQ.x1*kQ.x3 - (p^2)*kQ.x2*kQ.x3 - kQ.x1*kQ.x4 + kQ.x2*kQ.x4) ;
	C:= GBQuotient( kQ, rels );
	return [ C, kQ, rels ];
end;



AlgebraD:= function( K, p, h ) #no restriction on p
	local kQ, rels, D, x1, x2, x3, x4;
	kQ:= FreeKAlgebraNoGeneratorNames( K, 4, "x" );
	rels:= [];
	
	#wx + xw
	rels[1]:= kQ.x1*kQ.x2 + kQ.x2*kQ.x1 ;
	
	#zy - pyz
	rels[2]:= kQ.x4*kQ.x3 - p*kQ.x3*kQ.x4 ;

	#yw + pwy
	rels[3]:= kQ.x3*kQ.x1 + h*(p*kQ.x1*kQ.x3) ;
	
	#yx + p^2xy - wz
	rels[4]:= kQ.x3*kQ.x2 + h*((p*p)*kQ.x2*kQ.x3 - kQ.x1*kQ.x4) ;
	
	#zw - pwz
	rels[5]:= kQ.x4*kQ.x1 - h*(p*kQ.x1*kQ.x4) ;
	
	#zx - wy - xz
	rels[6]:= kQ.x4*kQ.x2 + h*(-kQ.x1*kQ.x3 - kQ.x2*kQ.x4) ;
	D:= GBQuotient( kQ, rels );
	return [ D, kQ, rels ];
end;



AlgebraE:= function( h )
	local kQ, p, rels, Ee, x1, x2, x3, x4;
	kQ:= FreeKAlgebraNoGeneratorNames( GaussianRationals, 4, "x" );
	p:= E(4);
	rels:= [];

	#xw + wx
	rels[1]:= kQ.x2*kQ.x1 + kQ.x1*kQ.x2 ;

	#zy - pwz
	rels[2]:= kQ.x4*kQ.x3 - p*kQ.x3*kQ.x4 ;

	#yw - wz - xz
	rels[3]:= kQ.x3*kQ.x1 + h*(-kQ.x1*kQ.x4 - kQ.x2*kQ.x4 ) ;

	#yx - wz + xz
	rels[4]:= kQ.x3*kQ.x2 + h*(-kQ.x1*kQ.x4 + kQ.x2*kQ.x4 ) ;

	#zw + wy - xy
	rels[5]:= kQ.x4*kQ.x1 + h*(kQ.x1*kQ.x3 - kQ.x2*kQ.x3 ) ;

	#zx - wy - xy
	rels[6]:= kQ.x4*kQ.x2 + h*(-kQ.x1*kQ.x3 - kQ.x2*kQ.x3 ) ;
	Ee:= GBQuotient( kQ, rels );
	return [ Ee, kQ, rels ];
end;



AlgebraF:= function( h )
	local kQ, p, rels, F, x1, x2, x3, x4;
	kQ:= FreeKAlgebraNoGeneratorNames( GaussianRationals, 4, "x" );
	p:= E(4);
	rels:= [ ];

	#xw + wx
	rels[1]:= kQ.x2*kQ.x1 + kQ.x1*kQ.x2 ;
	
	#zy - pyz
	rels[2]:= kQ.x4*kQ.x3 - p*kQ.x3*kQ.x4 ;
	
	#yw + wy + pxy - wz + xz
	rels[3]:= kQ.x3*kQ.x1 + h*(kQ.x1*kQ.x3 + p*kQ.x2*kQ.x3 - kQ.x1*kQ.x4 + kQ.x2*kQ.x4) ;
	
	#yx + pwy - xy - wz - xz
	rels[4]:= kQ.x3*kQ.x2 + h*(p*kQ.x1*kQ.x3 - kQ.x2*kQ.x3 - kQ.x1*kQ.x4 - kQ.x2*kQ.x4 );
	
	#zw + pwy - pxy - pwz - xz
	rels[5]:= kQ.x4*kQ.x1 + h*(p*kQ.x1*kQ.x3 - p*kQ.x2*kQ.x3 - p*kQ.x1*kQ.x4 - kQ.x2*kQ.x4) ;

	#zx + pwy + pxy - wz + pxz
	rels[6]:= kQ.x4*kQ.x2 + h*(p*kQ.x1*kQ.x3 + p*kQ.x2*kQ.x3 - kQ.x1*kQ.x4 + p*kQ.x2*kQ.x4) ;
	F:= GBQuotient( kQ, rels );
	return [ F, kQ, rels ];
end;



AlgebraG:= function( K, p, f, h )
	local kQ, rels, G, x1, x2, x3, x4;
	kQ:= FreeKAlgebraNoGeneratorNames( K, 4, "x" );
	rels:= [];
	if f = Zero( kQ ) then
		Error( "f needs to be nonzero" );
	else
		#wx - wx
		rels[1]:= kQ.x2*kQ.x1 - kQ.x1*kQ.x2 ;

		#zy - pyz
		rels[2]:= kQ.x4*kQ.x3 - p*kQ.x3*kQ.x4 ;

		#yw - pwy
		rels[3]:= kQ.x3*kQ.x1 + h*(-p*kQ.x1*kQ.x3) ;

		#yx - pwy - p^2xy - wz
		rels[4]:= kQ.x3*kQ.x2 + h*(-p*kQ.x1*kQ.x3 - (p*p)*kQ.x2*kQ.x3 - kQ.x1*kQ.x4);

		#zw - pwz
		rels[5]:= kQ.x4*kQ.x1 + h*(-p*kQ.x1*kQ.x4) ;

		#zx - fwy + wz - xz
		rels[6]:= kQ.x4*kQ.x2 + h*(-f*kQ.x1*kQ.x3 + kQ.x1*kQ.x4 - kQ.x2*kQ.x4 );
		G:= GBQuotient( kQ, rels );
		return [G, kQ, rels] ;
	fi;
end;



AlgebraH:= function( K, f, h )
	local kQ, rels, x1, x2, x3, x4, I, gb, A ;
	kQ:= FreeKAlgebraNoGeneratorNames( K, 4, "x" );
	x1:= kQ.x1; x2:= kQ.x2; x3:= kQ.x3; x4:= kQ.x4;
	rels:= [];

	#xw - wx - w^2
	rels[1]:= x2*x1 - x1*x2 - x1^2 ;

	#zy + yz
	rels[2]:= x4*x3 + x3*x4 ;

	#yw - wz
	rels[3]:= x3*x1 - h*x1*x4 ;

	#yx - fwz - xz
	rels[4]:= x3*x2 - h*f*x1*x4 - h*x2*x4 ;

	#zw - wy
	rels[5]:= x4*x1 - h*x1*x3 ;

	#zx - fwy - xy
	rels[6]:= x4*x2 - h*f*x1*x3 - h*x2*x3 ;
	#	I:= Ideal( kQ, rels );
	#	gb:= GroebnerBasis( I, rels );
	A:= kQ/rels ;
	#	A:= GBQuotient( kQ, rels );
	return [ A, kQ, rels ] ;
end;



AlgebraI:= function( h )   #Need to find a way to encode q^2 = -1 # Use the function FieldExtension
	local kQ, rels, q, I, J, x1, x2, x3, x4;
	kQ:= FreeKAlgebraNoGeneratorNames( GaussianRationals, 4, "x" );
	q:= E(4);
	rels:= [ ];

	#wx - qwx
	rels[1]:= kQ.x2*kQ.x1 - q*kQ.x1*kQ.x2 ;

	#zy + yz
	rels[2]:= kQ.x4*kQ.x3 + kQ.x3*kQ.x4 ;

	#yw + qwy + qxy - wz + qxz
	rels[3]:= kQ.x3*kQ.x1 + h*(q*kQ.x1*kQ.x3 + q*kQ.x2*kQ.x3 - kQ.x1*kQ.x4 + q*kQ.x2*kQ.x4 ) ;

	#yx - wy - xy - wz + qxz
	rels[4]:= kQ.x3*kQ.x2 + h*(-kQ.x1*kQ.x3 - kQ.x2*kQ.x3 - kQ.x1*kQ.x4 + q*kQ.x2*kQ.x4 ) ;

	#zw - wy - qxy - qwz + qxz
	rels[5]:= kQ.x4*kQ.x1 + h*( -kQ.x1*kQ.x3 - q*kQ.x2*kQ.x3 - q*kQ.x1*kQ.x4 + q*kQ.x2*kQ.x4 ) ;

	#zx - wy + qxy - wz + xz
	rels[6]:= kQ.x4*kQ.x2 + h*(kQ.x1*kQ.x3 + q*kQ.x2*kQ.x3 - kQ.x1 * kQ.x4 + kQ.x2*kQ.x4 ) ;
#	J:= Ideal( kQ, rels );
	I:= GBQuotient( kQ, rels );
	return [I, kQ, rels ];
end;



AlgebraJ:= function( h )
	local kQ, rels, q, J, x1, x2, x3, x4;
	kQ:= FreeKAlgebraNoGeneratorNames( GaussianRationals, 4, "x" );
	q:= E(4);
	rels:= [];

	#xw - qwx
	rels[1]:= kQ.x2*kQ.x1 - q*kQ.x1*kQ.x2 ;

	#zy + yz
	rels[2]:= kQ.x4*kQ.x3 + kQ.x3*kQ.x4 ;

	#yw - xy - xz
	rels[3]:= kQ.x3*kQ.x1 + h*(-kQ.x2*kQ.x3 - kQ.x2*kQ.x4 ) ;

	#yx + wy - wz
	rels[4]:= kQ.x3*kQ.x2 + h*(kQ.x1*kQ.x3 - kQ.x1*kQ.x4 ) ;

	#zw - xy + xz
	rels[5]:= kQ.x4*kQ.x1 + h*(-kQ.x2*kQ.x3 + kQ.x2*kQ.x4 ) ;

	#zx - wy - wz
	rels[6]:= kQ.x4*kQ.x2 + h*(-kQ.x1*kQ.x3 - kQ.x1*kQ.x4 ) ;
	J:= GBQuotient( kQ, rels );
	return [ J, kQ, rels ];
end;



AlgebraK:= function( K, f, q, h )
	local kQ, rels, KAlg, x1, x2, x3, x4;
	kQ:= FreeKAlgebraNoGeneratorNames( K, 4, "x" );
	rels:= [];
	if f = Zero( K ) then
		Error("f needs to be nonzero");
	else

		#xw - qwx
		rels[1]:= kQ.x2*kQ.x1 - q*kQ.x1*kQ.x2 ;

		#zy + yz
		rels[2]:= kQ.x4*kQ.x3 + kQ.x3*kQ.x4 ;

		#yw - wy
		rels[3]:= kQ.x3*kQ.x1 + h*(-kQ.x1*kQ.x3) ;

		#yx - xz
		rels[4]:= kQ.x3*kQ.x2 + h*(-kQ.x2*kQ.x4) ;

		#zw - wz
		rels[5]:= kQ.x4*kQ.x1 + h*(-kQ.x1*kQ.x4) ;

		#zx - fxy
		rels[6]:= kQ.x4*kQ.x2 + h*(-f*kQ.x2*kQ.x3) ;
		KAlg:= GBQuotient( kQ, rels );
		return [ KAlg, kQ, rels ];
	fi;
end;



AlgebraL:= function( K, f, q, h )
	local kQ, rels, L, x1, x2, x3, x4;
	kQ:= FreeKAlgebraNoGeneratorNames( K, 4, "x" );
	rels:= [];
	if f = Zero( K ) then
		Error("f needs to be nonzero");
	else

		#xw - qwx
		rels[1]:= kQ.x2*kQ.x1 - q*kQ.x1*kQ.x2 ;

		#zy + yz
		rels[2]:= kQ.x4*kQ.x3 + kQ.x3*kQ.x4 ;

		#yw - fwz
		rels[3]:= kQ.x3*kQ.x1 + h*(-f*kQ.x1*kQ.x4) ;

		#yx - xz
		rels[4]:= kQ.x3*kQ.x2 + h*(-kQ.x2*kQ.x4) ;

		#zw - fwy
		rels[5]:= kQ.x4*kQ.x1 + h*(-f*kQ.x1*kQ.x3) ;

		#zx - xy
		rels[6]:= kQ.x4*kQ.x2 + h*(-kQ.x2*kQ.x3) ;
		L:= GBQuotient( kQ, rels );
		return [ L, kQ, rels ];
	fi;
end;



AlgebraM:= function( K, f, h )
	local kQ, rels, M, x1, x2, x3, x4;
	kQ:= FreeKAlgebraNoGeneratorNames( K, 4, "x" );
	if f = One( K ) then
		return "f cannot be 1";
	else
		rels:= [];

		#xw + wx
		rels[1]:= kQ.x2*kQ.x1 + kQ.x1*kQ.x2 ;

		#zy + yz
		rels[2]:= kQ.x4*kQ.x3 + kQ.x3*kQ.x4 ;

		#yw - xy - wz
		rels[3]:= kQ.x3*kQ.x1 + h*(-kQ.x2*kQ.x3 - kQ.x1*kQ.x4 ) ;

		#yx - fwy + xz
		rels[4]:= kQ.x3*kQ.x2 + h*(-f*kQ.x1*kQ.x3 + kQ.x2*kQ.x4 ) ;

		#zw - wy + xz
		rels[5]:= kQ.x4*kQ.x1 + h*(-kQ.x1*kQ.x3 + kQ.x2*kQ.x4 ) ;

		#zw + xy + fwz
		rels[6]:= kQ.x4*kQ.x2 + h*(kQ.x2*kQ.x3 + f*kQ.x1*kQ.x4 ) ;;
		M:= GBQuotient( kQ, rels );
		return [ M, kQ, rels ];
	fi;
end;



AlgebraN:= function( K, f, g, h )
	local kQ, rels, N, x1, x2, x3, x4;
	kQ:= FreeKAlgebraNoGeneratorNames( K, 4, "x" );
	if f^2 = g^2 then
		return "f^2 cannot equal g^2";
	else
		rels:= [];

		#xw + wx
		rels[1]:= kQ.x2*kQ.x1 + kQ.x1*kQ.x2 ;

		#zy + yz
		rels[2]:= kQ.x4*kQ.x3 + kQ.x3*kQ.x4 ;

		#yw + gxy - fxz
		rels[3]:= kQ.x3*kQ.x1 + h*(g*kQ.x2*kQ.x3 - f*kQ.x2*kQ.x4 ) ;

		#yx - gwy - fwz
		rels[4]:= kQ.x3*kQ.x2 + h*(-g*kQ.x1*kQ.x3 - f*kQ.x1*kQ.x4 ) ;

		#zw - fxy + gxz
		rels[5]:= kQ.x4*kQ.x1 + h*(-f*kQ.x2*kQ.x3 + g*kQ.x2*kQ.x4 ) ;

		#zw - fwy - gwz
		rels[6]:= kQ.x4*kQ.x2 + h*(-f*kQ.x1*kQ.x3 - g*kQ.x1*kQ.x4 ) ;
		N:= GBQuotient( kQ, rels );
		return [ N, kQ, rels ];
	fi;
end;


AlgebraO:= function( K, f, h )
	local kQ, rels, I, O, x1, x2, x3, x4;
	kQ:= FreeKAlgebraNoGeneratorNames( K, 4, "x" );
	if f = One( K ) then
		return "f cannot be 1";
	else
		rels:= [ ];

		#xw + wx
		rels[1]:= kQ.x2*kQ.x1 + kQ.x1*kQ.x2 ;

		#zy + yz
		rels[2]:= kQ.x4*kQ.x3 + kQ.x3*kQ.x4 ;

		#yw - wy - fxz
		rels[3]:= kQ.x3*kQ.x1 + h*(-kQ.x1*kQ.x3 - f*kQ.x2*kQ.x4 ) ;

		#yx + xy - wz
		rels[4]:= kQ.x3*kQ.x2 + h*(kQ.x2*kQ.x3 - kQ.x1*kQ.x4 ) ;

		#zw - fxy + wz
		rels[5]:= kQ.x4*kQ.x1 + h*(-f*kQ.x2*kQ.x3 + kQ.x1*kQ.x4 ) ;

		#zx - wy - xz
		rels[6]:= kQ.x4*kQ.x2 + h*(-kQ.x1*kQ.x3 - kQ.x2*kQ.x4 ) ;
		O:= GBQuotient( kQ, rels );
		return [ O, kQ, rels ];
	fi;
end;


AlgebraP:= function( K, f, h ) #Check for f = 0
	local kQ, rels, I, Palg, x1, x2, x3, x4;
	kQ:= FreeKAlgebraNoGeneratorNames( K, 4, "x" );
	if f = One( K ) then
		return "f cannot be 1";
	else
		rels:= [ ];

		#xw + wx
		rels[1]:= kQ.x2*kQ.x1 + kQ.x1*kQ.x2 ;

		#zy + yz
		rels[2]:= kQ.x4*kQ.x3 + kQ.x3*kQ.x4 ;

		#yw - wz - fxz
		rels[3]:= kQ.x3*kQ.x1 + h*(-kQ.x1*kQ.x4 - f*kQ.x2*kQ.x4 ) ;

		#yx - wz - xz
		rels[4]:= kQ.x3*kQ.x2 + h*(-kQ.x1*kQ.x4 - kQ.x2*kQ.x4 ) ;

		#zw - wy + fxy
		rels[5]:= kQ.x4*kQ.x1 + h*(-kQ.x1*kQ.x3 + f*kQ.x2*kQ.x3 ) ;

		#zx + wy - xy
		rels[6]:= kQ.x4*kQ.x2 + h*(kQ.x1*kQ.x3 - kQ.x2*kQ.x3 ) ;
		Palg:= GBQuotient( kQ, rels );
		return [ Palg, kQ, rels ];
	fi;
end;


AlgebraQ:= function( K, h )
	local kQ, rels, I, Q, x1, x2, x3, x4;
	kQ:= FreeKAlgebraNoGeneratorNames( K, 4, "x" );
	rels:= [ ];

	#xw + wx
	rels[1]:= kQ.x2*kQ.x1 + kQ.x1*kQ.x2 ;

	#zy + yz
	rels[2]:= kQ.x4*kQ.x3 + kQ.x3*kQ.x4 ;

	#yw - wz
	rels[3]:= kQ.x3*kQ.x1 + h*(-kQ.x1*kQ.x4) ;

	#yx - wy - xy - wz
	rels[4]:= kQ.x3*kQ.x2 + h*(-kQ.x1*kQ.x3 - kQ.x2*kQ.x3 - kQ.x1*kQ.x4 ) ;

	#zw + wy
	rels[5]:= kQ.x4*kQ.x1 + h*(kQ.x1*kQ.x3 ) ;

	#zx - wy + wz - xz
	rels[6]:= kQ.x4*kQ.x2 + h*(-kQ.x1*kQ.x3 + kQ.x1*kQ.x4 - kQ.x2*kQ.x4 ) ;
	Q:= GBQuotient( kQ, rels );
	return [ Q, kQ, rels ];
end;


AlgebraR:= function( K, h )
	local kQ, rels, I, R, x1, x2, x3, x4;
	kQ:= FreeKAlgebraNoGeneratorNames( K, 4, "x" );
	rels:= [ ];

	#xw + wx
	rels[1]:= kQ.x2*kQ.x1 + kQ.x1*kQ.x2 ;

	#zy + yz
	rels[2]:= kQ.x4*kQ.x3 + kQ.x3*kQ.x4 ;

	#yw - wy - xy - wz
	rels[3]:= kQ.x3*kQ.x1 + h*(-kQ.x1*kQ.x3 - kQ.x2*kQ.x3 - kQ.x1*kQ.x4 ) ;

	#yx - wz
	rels[4]:= kQ.x3*kQ.x2 + h*(-kQ.x1*kQ.x4 ) ;

	#zw - xy
	rels[5]:= kQ.x4*kQ.x1 + h*(-kQ.x2*kQ.x3 ) ;

	#zx + xy + wz - xz
	rels[6]:= kQ.x4*kQ.x2 + h*(kQ.x2*kQ.x3 + kQ.x1*kQ.x4 - kQ.x2*kQ.x4 );
	R:= GBQuotient( kQ, rels );
	return [ R, kQ, rels ];
end;


AlgebraS:= function( K, h )
	local kQ, rels, x1, x2, x3, x4, I, gb, A ;
	kQ:= FreeKAlgebraNoGeneratorNames( K, 4, "x" );
	x1:= kQ.x1; x2:= kQ.x2; x3:= kQ.x3; x4:= kQ.x4;
	rels:= [];

	#xw + wx
	rels[1]:= x2*x1 + x1*x2 ;

	#zy + yz
	rels[2]:= x4*x3 + x3*x4 ;

	#yw + wy - xy - wz - xz
	rels[3]:= x3*x1 + h*(x1*x3 - x2*x3 - x1*x4 - x2*x4 ) ;

	#yx - wy + xy - wz - xz
	rels[4]:= x3*x2 + h*(-x1*x3 + x2*x3 - x1*x4 - x2*x4 ) ;

	#zw - wy - xy + wz - xz
	rels[5]:= x4*x1 + h*(-x1*x3 - x2*x3 + x1*x4 - x2*x4 ) ;

	#zx - wy - xy - wz + xz
	rels[6]:= x4*x2 + h*(-x1*x3 - x2*x3 - x1*x4 + x2*x4 ) ;
	#	I:= Ideal( kQ, rels );
	#	gb:= GroebnerBasis( I, rels );
	A:= kQ/rels ;
	#	A:= GBQuotient( kQ, rels );
	return [ A, kQ, rels ] ;
end;


AlgebraT:= function( K, h )
	local kQ, rels, I, T, x1, x2, x3, x4;
	kQ:= FreeKAlgebraNoGeneratorNames( K, 4, "x" );
	rels:= [];

	#xw + wx
	rels[1]:= kQ.x2*kQ.x1 + kQ.x1*kQ.x2 ;

	#zy + yz
	rels[2]:= kQ.x4*kQ.x3 + kQ.x3*kQ.x4 ;

	#yw + wy - xy - wz - xz
	rels[3]:= kQ.x3*kQ.x1 + h*(kQ.x1*kQ.x3 - kQ.x2*kQ.x3 - kQ.x1*kQ.x4 - kQ.x2*kQ.x4 ) ;

	#yw - wy + xy - wz - xz
	rels[4]:= kQ.x3*kQ.x2 + h*(-kQ.x1*kQ.x3 + kQ.x2*kQ.x3 - kQ.x1*kQ.x4 - kQ.x2*kQ.x4 ) ;

	#zw - wy - xy - wz + xz
	rels[5]:= kQ.x4*kQ.x1 + h*(-kQ.x1*kQ.x3 - kQ.x2*kQ.x3 - kQ.x1*kQ.x4 + kQ.x2*kQ.x4 ) ;

	#zx - wy - xy + wz - xz
	rels[6]:= kQ.x4*kQ.x2 + h*(-kQ.x1*kQ.x3 - kQ.x2*kQ.x3 + kQ.x1*kQ.x4 - kQ.x2*kQ.x4 ) ;
	T:= GBQuotient( kQ, rels );
	return [ T, kQ, rels ];
end;


AlgebraU:= function( K,  h )
	local kQ, rels, x1, x2, x3, x4, I, gb, A ;
	kQ:= FreeKAlgebraNoGeneratorNames( K, 4, "x" );
	x1:= kQ.x1; x2:= kQ.x2; x3:= kQ.x3; x4:= kQ.x4;
	rels:= [];

	#xw + wx
	rels[1]:= x2*x1 + x1*x2 ;

	#zy + yz
	rels[2]:= x4*x3 + x3*x4 ;

	#yw + wy - xy - wz - xz
	rels[3]:= x3*x1 + h*(x1*x3 - x2*x3 - x1*x4 - x2*x4 ) ;

	#yx - wy - xy - wz + xz
	rels[4]:= x3*x2 + h*(-x1*x3 - x2*x3 - x1*x4 + x2*x4 ) ;

	#zw - wy - xy + wz - xz
	rels[5]:= x4*x1 + h*(-x1*x3 - x2*x3 + x1*x4 - x2*x4 ) ;

	#zx - wy + xy - wz - xz
	rels[6]:= x4*x2 + h*(-x1*x3 + x2*x3 - x1*x4 - x2*x4 ) ;
	#	I:= Ideal( kQ, rels );
	#	gb:= GroebnerBasis( I, rels );
	A:= kQ/rels ;
	#	A:= GBQuotient( kQ, rels );
	return [ A, kQ, rels ] ;
end;


AlgebraV:= function( K, h )
	local kQ, rels, x1, x2, x3, x4, I, gb, A ;
	kQ:= FreeKAlgebraNoGeneratorNames( K, 4, "x" );
	x1:= kQ.x1; x2:= kQ.x2; x3:= kQ.x3; x4:= kQ.x4;
	rels:= [];

	#xw - wx
	rels[1]:= x2*x1 - x1*x2 ;

	#zy + yz
	rels[2]:= x4*x3 + x3*x4 ;

	#yw - xy - wz
	rels[3]:= x3*x1 + h*(-x2*x3 - x1*x4 ) ;

	#yx - xy
	rels[4]:= x3*x2 - h*x2*x3 ;

	#zw + wy - xy
	rels[5]:= x4*x1 + h*(x1*x3 - x2*x3 ) ;

	#zx - wz
	rels[6]:= x4*x2 - h*x2*x4 ;
	#	I:= Ideal( kQ, rels );
	#	gb:= GroebnerBasis( I, rels );
	A:= kQ/rels ;
	#	A:= GBQuotient( kQ, rels );
	return [ A, kQ, rels ] ;
end;


AlgebraW:= function( K, f, h ) #f \neq -1
	local kQ, rels, x1, x2, x3, x4, I, gb, A ;
	kQ:= FreeKAlgebraNoGeneratorNames( K, 4, "x" );
	x1:= kQ.x1; x2:= kQ.x2; x3:= kQ.x3; x4:= kQ.x4;
	rels:= [];

	#xw - wx
	rels[1]:= x2*x1 - x1*x2 ;

	#zw + wz
	rels[2]:= x4*x3 + x3*x4 ;

	#yw - fxy - wz
	rels[3]:= x3*x1 + h*(-f*x2*x3 - x1*x4 ) ;

	#yx - wy + xz
	rels[4]:= x3*x2 + h*(-x1*x3 + x2*x4 ) ;

	#zw - wy - fxz
	rels[5]:= x4*x1 + h*(-x1*x3 - f*x2*x4 ) ;

	#zy + xy - wz
	rels[6]:= x4*x2 + h*(x2*x3 - x1*x4 ) ;
	#	I:= Ideal( kQ, rels );
	#	gb:= GroebnerBasis( I, rels );
	A:= kQ/rels ;
	#	A:= GBQuotient( kQ, rels );
	return [ A, kQ, rels ] ;
end;


AlgebraX:= function( K, h )
	local kQ, rels, x1, x2, x3, x4, I, gb, A ;
	kQ:= FreeKAlgebraNoGeneratorNames( K, 4, "x" );
	x1:= kQ.x1; x2:= kQ.x2; x3:= kQ.x3; x4:= kQ.x4;
	rels:= [];

	#xw - wx
	rels[1]:= x2*x1 - x1*x2 ;

	#zy + yz
	rels[2]:= x4*x3 + x3*x4 ;

	#yw - wz
	rels[3]:= x3*x1 + h*(-x1*x4) ;

	#yx - wz - xz
	rels[4]:= x3*x2 + h*(-x1*x4 - x2*x4 ) ;

	#zw - wy
	rels[5]:= x4*x1 + h*(-x1*x3 ) ;

	#zx - wy - xy
	rels[6]:= x4*x2 + h*(-x1*x3 - x2*x3 ) ;
	#	I:= Ideal( kQ, rels );
	#	gb:= GroebnerBasis( I, rels );
	A:= kQ/rels ;
	#	A:= GBQuotient( kQ, rels );
	return [ A, kQ, rels ] ;
end;


AlgebraY:= function( K, f, h )
	local kQ, rels, x1, x2, x3, x4, I, gb, A ;
	kQ:= FreeKAlgebraNoGeneratorNames( K, 4, "x" );
	x1:= kQ.x1; x2:= kQ.x2; x3:= kQ.x3; x4:= kQ.x4;
	rels:= [];

	#xw - wx
	rels[1]:= x2*x1 - x1*x2 ;

	#zy + yz 
	rels[2]:= x4*x3 + x3*x4 ;

	#yw - wy
	rels[3]:= x3*x1 + h*(-x1*x3) ;

	#yx - fwy + xy
	rels[4]:= x3*x2 + h*(-f*x1*x3 + x2*x3 - x1*x4 ) ;

	#zw - wz
	rels[5]:= x4*x1 + h*(-x1*x4 ) ;

	#zx - wy - fwz + xz
	rels[6]:= x4*x2 + h*(-x1*x3 - f*x1*x4 + x2*x4 ) ;
	#	I:= Ideal( kQ, rels );
	#	gb:= GroebnerBasis( I, rels );
	A:= kQ/rels ;
	#	A:= GBQuotient( kQ, rels );
	return [ A, kQ, rels ] ;
end;



AlgebraZ:= function( K, f, h ) #need f(f+1) != 0
	local kQ, rels, I, Zalg, x1, x2, x3, x4;
	kQ:= FreeKAlgebraNoGeneratorNames( K, 4, "x" );
#	if f*(1+f) = 0 then
#		Print( "Need f(1+f) != 0" );
#	else
		rels:= [ ];
		
		#xw + wx
		rels[1]:= kQ.x2*kQ.x1 + kQ.x1*kQ.x2 ;

		#zy - yz
		rels[2]:= kQ.x4*kQ.x3 - kQ.x3*kQ.x4 ;

		#yw - wy - xz
		rels[3]:= kQ.x3*kQ.x1 + h*(-kQ.x1*kQ.x3 - kQ.x2*kQ.x4 ) ;

		#yx - xy - wz
		rels[4]:= kQ.x3*kQ.x2 + h*(-kQ.x2*kQ.x3 - kQ.x1*kQ.x4 ) ;

		#zw - fxy + wz
		rels[5]:= kQ.x4*kQ.x1 + h*(-f*kQ.x2*kQ.x3 + kQ.x1*kQ.x4 ) ;

		#zw - fwy + xz
		rels[6]:= kQ.x4*kQ.x2 + h*(-f*kQ.x1*kQ.x3 + kQ.x2*kQ.x4 ) ;
#		I:= Ideal( kQ, rels );
		Zalg:= GBQuotient( kQ, rels );
#		Zalg:= kQ/I ;
		return [ Zalg, kQ, rels ];
#	fi;
end;



#AlgebraZ:= function( K, f ) #need f(f+1) != 0
#	local kQ, rels, I, Zalg, x1, x2, x3, x4;
#	kQ:= FreeKAlgebraNoGeneratorNames( K, 4, "x" );
#	if f*(1+f) = 0 then
#		Print( "Need f(1+f) != 0" );
#	else
#		rels:= [ ];
#		rels[1]:= kQ.x1*kQ.x2 + kQ.x2*kQ.x1 ;
#		rels[2]:= kQ.x4*kQ.x3 - kQ.x3*kQ.x4 ;
#		rels[3]:= kQ.x3*kQ.x1 - kQ.x1*kQ.x4 - kQ.x2*kQ.x4 ;
#		rels[4]:= kQ.x3*kQ.x2 - kQ.x2*kQ.x3 - kQ.x1*kQ.x4 ;
#		rels[5]:= kQ.x4*kQ.x1 - f*kQ.x2*kQ.x3 + kQ.x1*kQ.x4 ;
#		rels[6]:= kQ.x4*kQ.x2 - f*kQ.x1*kQ.x4 + kQ.x2*kQ.x4 ;
#		I:= Ideal( kQ, rels );
#		Zalg:= GBQuotient( kQ, rels );
#		Zalg:= kQ/I ;
#		return [ 0, kQ, rels ];
#	fi;
#end;


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
#	A:= GBQuotient( kQ, rels );
	return [ 0, kQ, rels ] ;
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



CocycleTwistElementf:= function( kQ, alpha, beta, gamma, i )
	local f ;
	if i = 1 then
		f:= Commutator( kQ.x1, kQ.x2 ) - alpha*SkewCommutator( kQ.x3, kQ.x4 ) ;
	elif i = 2 then
		f:=	SkewCommutator( kQ.x1, kQ.x2 ) - Commutator( kQ.x3, kQ.x4 ) ;
	elif i = 3 then
		f:= Commutator( kQ.x1, kQ.x3 ) - beta*SkewCommutator( kQ.x4, kQ.x2 );
	elif i = 4 then
		f:= SkewCommutator( kQ.x1, kQ.x3 ) - Commutator( kQ.x4, kQ.x2 );
	elif i = 5 then
		f:= Commutator( kQ.x1, kQ.x4 ) - gamma*SkewCommutator( kQ.x2, kQ.x3 ) ;
	elif i = 6 then
		f:= SkewCommutator( kQ.x1, kQ.x4 ) - Commutator( kQ.x2, kQ.x3 );
	fi;
	return f;
end;



CocycleTwistElementfmu:= function( kQ, alpha, beta, gamma, i )
	local f ;
	if i = 1 then
		f:= Commutator( kQ.x1, kQ.x2 ) - alpha*Commutator( kQ.x3, kQ.x4 ) ;
	elif i = 2 then
		f:=	SkewCommutator( kQ.x1, kQ.x2 ) - SkewCommutator( kQ.x3, kQ.x4 ) ;
	elif i = 3 then
		f:= Commutator( kQ.x1, kQ.x3 ) - beta*Commutator( kQ.x4, kQ.x2 );
	elif i = 4 then
		f:= SkewCommutator( kQ.x1, kQ.x3 ) - SkewCommutator( kQ.x4, kQ.x2 );
	elif i = 5 then
		f:= Commutator( kQ.x1, kQ.x4 ) + gamma*Commutator( kQ.x2, kQ.x3 ) ;
	elif i = 6 then
		f:= SkewCommutator( kQ.x1, kQ.x4 ) + SkewCommutator( kQ.x2, kQ.x3 );
	fi;
	return f;
end;



4dSklyaninAlgebra:= function( K, beta, gamma )	#(1.1.16), where alpha, beta and gamma are nonzero and not +-1
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
#	I:= Ideal( kQ, rels );
#	gb:= GroebnerBasis( I, rels );
#	A:= kQ/I ;
#	A:= GBQuotient( kQ, rels );
	return [ 0, kQ, rels ];
end;



4dSklyaninAlgebraTwist:= function( K, beta, gamma )	#(4.1.4), where alpha, beta and gamma are nonzero and not +-1, p.90
	local kQ, alpha, rels, I, gb, A ;
	alpha:= -(beta + gamma)/(1 + beta*gamma) ;
	kQ:= FreeKAlgebra( K, 4, "x" );
	rels:= [ ];
	rels[1]:= Commutator( kQ.x1, kQ.x2 ) - alpha*Commutator( kQ.x3, kQ.x4 ) ;
	rels[2]:= SkewCommutator( kQ.x1, kQ.x2 ) - SkewCommutator( kQ.x3, kQ.x4 ) ;
	rels[3]:= Commutator( kQ.x1, kQ.x3 ) - beta*Commutator( kQ.x4, kQ.x2 );
	rels[4]:= SkewCommutator( kQ.x1, kQ.x3 ) - SkewCommutator( kQ.x4, kQ.x2 );
	rels[5]:= Commutator( kQ.x1, kQ.x4 ) + gamma*Commutator( kQ.x2, kQ.x3 ) ;
	rels[6]:= SkewCommutator( kQ.x1, kQ.x4 ) + SkewCommutator( kQ.x2, kQ.x3 );
#	I:= Ideal( kQ, rels );
#	gb:= GroebnerBasis( I, rels );
#	A:= kQ/I ;
#	A:= GBQuotient( kQ, rels );
	return [ 0, kQ, rels ];
end;

#S stands for Stafford

AlgebraSInfinity:= function( K, beta, gamma )	#(6.1.3), where alpha, beta and gamma are nonzero and not +-1. p.140
	local kQ, alpha, rels, x1, x2, x3, x4, I, gb, A ;
	alpha:= -(beta + gamma)/(1 + beta*gamma) ;
	kQ:= FreeKAlgebra( K, 4, "x" );
	x1:= kQ.x1; x2:= kQ.x2; x3:= kQ.x3; x4:= kQ.x4;
	rels:= [ ];
	rels[1]:= Commutator( kQ.x1, kQ.x2 ) - alpha*SkewCommutator( kQ.x3, kQ.x4 ) ;
	rels[2]:= SkewCommutator( kQ.x1, kQ.x2 ) - Commutator( kQ.x3, kQ.x4 ) ;
	rels[3]:= Commutator( kQ.x1, kQ.x3 ) - beta*SkewCommutator( kQ.x4, kQ.x2 );
	rels[4]:= SkewCommutator( kQ.x1, kQ.x3 ) - Commutator( kQ.x4, kQ.x2 );
	rels[5]:= -x1^2 + x2^2 + x3^2 + x4^2 ;
	rels[6]:= x2^2 + ((1+alpha)/(1-beta))*x3^2 + ((1-alpha)/(1+gamma))*x4^2 ;
	#	I:= Ideal( kQ, rels );
	#	gb:= GroebnerBasis( I, rels );
#	A:= kQ/rels ;
	#	A:= GBQuotient( kQ, rels );
	return [ 0, kQ, rels ];
end;



AlgebraSdi:= function( K, i, d1, d2, beta, gamma )	#(6.1.4), where alpha, beta and gamma are nonzero and not +-1. p.140
	local kQ, alpha, rels, x1, x2, x3, x4, j, I, gb, A ;
	alpha:= -(beta + gamma)/(1 + beta*gamma) ;
	kQ:= FreeKAlgebra( K, 4, "x" );
	x1:= kQ.x1; x2:= kQ.x2; x3:= kQ.x3; x4:= kQ.x4;
	rels:= [ ];
	for j in [1..6] do
		if i = j then
			Add( rels, d1*(-x1^2 + x2^2 + x3^2 + x4^2) + d2*(x2^2 + ((1+alpha)/(1-beta))*x3^2 + ((1-alpha)/(1+gamma))*x4^2) ) ;
		else
			Add( rels, CocycleTwistElementf( kQ, alpha, beta, gamma, j ) );
		fi;
	od;
	#	I:= Ideal( kQ, rels );
	#	gb:= GroebnerBasis( I, rels );
#	A:= kQ/rels ;
	#	A:= GBQuotient( kQ, rels );
	return [ 0, kQ, rels ];
end;



AlgebraSInfinityTwist:= function( K, beta, gamma )	#(6.1.3), where alpha, beta and gamma are nonzero and not +-1. p.140
	local kQ, alpha, rels, x1, x2, x3, x4, I, gb, A ;
	alpha:= -(beta + gamma)/(1 + beta*gamma) ;
	kQ:= FreeKAlgebra( K, 4, "x" );
	x1:= kQ.x1; x2:= kQ.x2; x3:= kQ.x3; x4:= kQ.x4;
	rels:= [ ];
	rels[1]:= Commutator( kQ.x1, kQ.x2 ) - alpha*Commutator( kQ.x3, kQ.x4 ) ;
	rels[2]:= SkewCommutator( kQ.x1, kQ.x2 ) - SkewCommutator( kQ.x3, kQ.x4 ) ;
	rels[3]:= Commutator( kQ.x1, kQ.x3 ) - beta*Commutator( kQ.x4, kQ.x2 );
	rels[4]:= SkewCommutator( kQ.x1, kQ.x3 ) - SkewCommutator( kQ.x4, kQ.x2 );
	rels[5]:= -x1^2 + x2^2 + x3^2 - x4^2 ;
	rels[6]:= x2^2 + ((1+alpha)/(1-beta))*x3^2 - ((1-alpha)/(1+gamma))*x4^2 ;
	#	I:= Ideal( kQ, rels );
	#	gb:= GroebnerBasis( I, rels );
#	A:= kQ/rels ;
	#	A:= GBQuotient( kQ, rels );
	return [ 0, kQ, rels ];
end;



AlgebraSdiTwist:= function( K, i, d1, d2, beta, gamma )	#(6.1.4), where alpha, beta and gamma are nonzero and not +-1. p.141
																												#For this algebra to be AS regular of dimension 4, we need to assume,
																												#if i = 1, that (d1,d2) != (1,0), (1,-1-beta*gamma), and if i = 2,
																												#(d1,d2) != (1, beta-1), (1,-1-gamma)
	local kQ, alpha, rels, x1, x2, x3, x4, j, I, gb, A ;
	alpha:= -(beta + gamma)/(1 + beta*gamma) ;
	kQ:= FreeKAlgebra( K, 4, "x" );
	x1:= kQ.x1; x2:= kQ.x2; x3:= kQ.x3; x4:= kQ.x4;
	rels:= [ ];
	for j in [1..6] do
		if i = j then
			Add( rels, d1*(-x1^2 + x2^2 + x3^2 - x4^2) + d2*(x2^2 + ((1+alpha)/(1-beta))*x3^2 - ((1-alpha)/(1+gamma))*x4^2) ) ;
		else
			Add( rels, CocycleTwistElementfmu( kQ, alpha, beta, gamma, j ) );
		fi;
	od;
	#	I:= Ideal( kQ, rels );
	#	gb:= GroebnerBasis( I, rels );
#	A:= kQ/rels ;
	#	A:= GBQuotient( kQ, rels );
	return [ 0, kQ, rels ];
end;



AlgebraVancliff:= function( K, alpha, beta, lambda )	#(6.3.1), p.154
																											#lambda \neq alpha*beta
	local kQ, p, rels, x1, x2, x3, x4, I, gb, A;
	kQ:= FreeKAlgebra( K, 4, "x" );
#	p:= E(4);
	x1:= kQ.x1; x2:= kQ.x2; x3:= kQ.x3; x4:= kQ.x4;
	rels:= [ ];
	rels[1]:= x2*x1 - alpha*x1*x2 ;
	rels[2]:= x3*x1 - lambda*x1*x3 ;
	rels[3]:= x4*x1 - alpha*lambda*x1*x4 ;
	rels[4]:= x4*x3 - alpha*x3*x4 ;
	rels[5]:= x4*x2 - lambda*x2*x4 ;
	rels[6]:= x3*x2 - beta*x2*x3 - (alpha*beta - lambda)*x1*x4 ;
	#	I:= Ideal( kQ, rels );
	#	gb:= GroebnerBasis( I, rels );
	A:= kQ/rels ;
	#	A:= GBQuotient( kQ, rels );
	return [ A, kQ, rels ];
end;



AlgebraVancliffTwist:= function( K, alpha, beta, lambda )	#(6.3.6), p.155
																													#lambda \neq alpha*beta
	local kQ, p, rels, x1, x2, x3, x4, I, gb, A;
	kQ:= FreeKAlgebraNoGeneratorNames( K, 4, "x" );
#	p:= E(4);
	x1:= kQ.x1; x2:= kQ.x2; x3:= kQ.x3; x4:= kQ.x4;
	rels:= [ ];
	rels[1]:= x2*x1 - alpha*x1*x2 ;
	rels[2]:= x3*x1 - lambda*x1*x3 ;
	rels[3]:= x4*x1 - alpha*lambda*x1*x4 ;
	rels[4]:= x4*x3 + alpha*x3*x4 ;
	rels[5]:= x4*x2 + lambda*x2*x4 ;
	rels[6]:= x3*x2 + beta*x2*x3 - (alpha*beta - lambda)*x1*x4 ;
	#	I:= Ideal( kQ, rels );
	#	gb:= GroebnerBasis( I, rels );
	A:= kQ/rels ;
	#	A:= GBQuotient( kQ, rels );
	return [ A, kQ, rels ];
end;





#################################################################################################################################################################################



CliffordAlgebra:= function( K, CoeffList ) #CoefList is a list of 6 lists of elements of K
  local PolyRing, kQ,
  a121, a122, a123, a124,
  a131, a132, a133, a134,
  a141, a142, a143, a144,
  a231, a232, a233, a234,
  a241, a242, a243, a244,
  a341, a342, a343, a344,
  rels, gb, I, A;
#
  a121:= CoeffList[1][1]; a122:= CoeffList[1][2]; a123:= CoeffList[1][3]; a124:= CoeffList[1][4];
	a131:= CoeffList[2][1]; a132:= CoeffList[2][2]; a133:= CoeffList[2][3]; a134:= CoeffList[2][4];
	a141:= CoeffList[3][1]; a142:= CoeffList[3][2]; a143:= CoeffList[3][3]; a144:= CoeffList[3][4];
	a231:= CoeffList[4][1]; a232:= CoeffList[4][2]; a233:= CoeffList[4][3]; a234:= CoeffList[4][4];
	a241:= CoeffList[5][1]; a242:= CoeffList[5][2]; a243:= CoeffList[5][3]; a244:= CoeffList[5][4];
	a341:= CoeffList[6][1]; a342:= CoeffList[6][2]; a343:= CoeffList[6][3]; a344:= CoeffList[6][4];
#
  kQ:= FreeKAlgebra( K, 4, "x" );
  rels:= [];
  rels[1]:= kQ.x1*kQ.x2 + kQ.x2*kQ.x1 + a121*kQ.x1^2 + a122*kQ.x2^2 + a123*kQ.x3^2 + a124*kQ.x4^2 ;
  rels[2]:= kQ.x1*kQ.x3 + kQ.x3*kQ.x1 + a131*kQ.x1^2 + a132*kQ.x2^2 + a133*kQ.x3^2 + a134*kQ.x4^2 ;
  rels[3]:= kQ.x1*kQ.x4 + kQ.x4*kQ.x1 + a141*kQ.x1^2 + a142*kQ.x2^2 + a143*kQ.x3^2 + a144*kQ.x4^2 ;
  rels[4]:= kQ.x2*kQ.x3 + kQ.x3*kQ.x2 + a231*kQ.x1^2 + a232*kQ.x2^2 + a233*kQ.x3^2 + a234*kQ.x4^2 ;
  rels[5]:= kQ.x2*kQ.x4 + kQ.x4*kQ.x2 + a241*kQ.x1^2 + a242*kQ.x2^2 + a243*kQ.x3^2 + a244*kQ.x4^2 ;
  rels[6]:= kQ.x3*kQ.x4 + kQ.x4*kQ.x3 + a341*kQ.x1^2 + a342*kQ.x2^2 + a343*kQ.x3^2 + a344*kQ.x4^2 ;
  I:= Ideal( kQ, rels );
#  gb:= GroebnerBasis( I, rels );
#  A:= kQ/I ;
#  A:= GBQuotient( kQ, rels );
	A:= kQ/rels;
	return [ A, kQ, rels ] ;
end;


CliffordAlgebra2:= function( K, a121, a122, a123, a124, a341, a342, a343, a344 )
  local PolyRing, kQ, rels, gb, I, A;
  kQ:= FreeKAlgebra( K, 4, "x" );
  rels:= [];
  rels[1]:= kQ.x1*kQ.x2 + kQ.x2*kQ.x1 + a121*kQ.x1^2 + a122*kQ.x2^2 + a123*kQ.x3^2 + a124*kQ.x4^2 ;
  rels[2]:= kQ.x1*kQ.x3 + kQ.x3*kQ.x1 ;
  rels[3]:= kQ.x1*kQ.x4 + kQ.x4*kQ.x1 ;
  rels[4]:= kQ.x2*kQ.x3 + kQ.x3*kQ.x2 ;
  rels[5]:= kQ.x2*kQ.x4 + kQ.x4*kQ.x2 ;
  rels[6]:= kQ.x3*kQ.x4 + kQ.x4*kQ.x3 + a341*kQ.x1^2 + a342*kQ.x2^2 + a343*kQ.x3^2 + a344*kQ.x4^2 ;
#  I:= Ideal( kQ, rels );
#  gb:= GroebnerBasis( I, rels );
#  A:= kQ/I ;
  A:= GBQuotient( kQ, rels );
	return [ A, kQ, rels ] ;
end;



TetrahedronAlgebra:= function( K, q12, q13, q14, q23, q24, q34 )
  local PolyRing, kQ, rels, I, gb, A ;
  kQ:= FreeKAlgebra( K, 4, "x" );
  rels:= [];
  rels[1]:= kQ.x1*kQ.x2 - q12*kQ.x2*kQ.x1 ;
  rels[2]:= kQ.x1*kQ.x3 - q13*kQ.x3*kQ.x1 ;
  rels[3]:= kQ.x1*kQ.x4 - q14*kQ.x4*kQ.x1 ;
  rels[4]:= kQ.x2*kQ.x3 - q23*kQ.x3*kQ.x2 ;
  rels[5]:= kQ.x2*kQ.x4 - q24*kQ.x4*kQ.x2 ;
  rels[6]:= kQ.x3*kQ.x4 - q34*kQ.x4*kQ.x3 ;
	I:= Ideal( kQ, rels );
	gb:= GroebnerBasis( I, rels );
#	A:= kQ/I ;
	A:= GBQuotient( kQ, rels );
  return [ A, kQ, rels ] ;
end;



PolynomialRingInFourIndeterminates:= function( K )
	local kQ, rels, I, gb, A ;
	kQ:= FreeKAlgebra( K, 4, "x" ) ;
	rels:= [ ] ;
	rels[1]:= Commutator( kQ.x1, kQ.x2 ) ;
	rels[2]:= Commutator( kQ.x1, kQ.x3 ) ;
	rels[3]:= Commutator( kQ.x1, kQ.x4 ) ;
	rels[4]:= Commutator( kQ.x2, kQ.x3 ) ;
	rels[5]:= Commutator( kQ.x2, kQ.x4 ) ;
	rels[6]:= Commutator( kQ.x3, kQ.x4 ) ;
	I:= Ideal( kQ, rels );
	gb:= GroebnerBasis( I, rels );
	#  A:= kQ/I ;
	A:= GBQuotient( kQ, rels );
	return [ A, kQ, rels ] ;
 end;



 EmailAlgebra:= function( K, a, b, s1, s2, s3, s4 )	#a, b in K, s1, ..., s4 = +-1
	 																					#Need only cases (s1, ..., s4) = (+, +, +, +), (+, -, +, -), (+, +, -, -), (+, -, -, -), (+, +, +, -)
 	local kQ, alpha, rels, I, gb, A ;
 	kQ:= FreeKAlgebra( K, 4, "x" );
 	rels:= [ ];
 	rels[1]:= SkewCommutator( kQ.x1, kQ.x3 ) ;
	rels[2]:= SkewCommutator( kQ.x1, kQ.x4 ) ;
	rels[3]:= SkewCommutator( kQ.x2, kQ.x3 ) ;
	rels[4]:= SkewCommutator( kQ.x2, kQ.x4 ) ;
	rels[5]:= s1*kQ.x1^2 + s2*kQ.x2^2 + s3*kQ.x3^2 + s4*kQ.x4^2 ;
	rels[6]:= a*SkewCommutator( kQ.x1, kQ.x2 ) + b*SkewCommutator( kQ.x3, kQ.x4 );
 #	I:= Ideal( kQ, rels );
 #	gb:= GroebnerBasis( I, rels );
 #	A:= kQ/I ;
 	A:= kQ/rels ;
 #	A:= GBQuotient( kQ, rels );
 	return [ A, kQ, rels ];
 end;


#################################################################################################################################################################################

#The next algebras are taken from the paper "Graded Clifford Algebras and Graded Skew Clifford Algebras and their Role in the Classification of
#Artin-Schelter Regular Algebras", by Veerapen


SkewCliffordAlgebra:= function( K, Coeffs )	#Coeffs is a list of length n-1 of lists, where Coeff[1] has length n-1, Coeff[2] has length n-2,
																						#..., until Coeff[n-1] has length n - (n-1) = 1.
																						#For n = 4, this is exactly the Tetrahedron algebra
	local n, kQ, rels, gens, x, y, i, j, I, gb, A;
	n:= Length( Coeffs ) + 1 ;
	kQ:= FreeKAlgebra( K, n, "x" );
	gens:= NonOneGeneratorsOfAlgebra( kQ );
	rels:= [ ] ;
	for i in [1..Length(Coeffs)] do
		for j in [1..Length(Coeffs[i])] do
			Add( rels, gens[j+i]*gens[i] - Coeffs[i][j]*gens[i]*gens[j+i] ) ;
		od;
	od;
	# I:= Ideal( kQ, rels );
	# gb:= GroebnerBasis( I, rels );
  A:= kQ/rels ;
	# A:= GBQuotient( kQ, rels );
	return [ A, kQ, rels ];
#	return gens;
end;


#################################################################################################################################################################################

#The next algebras are taken from the paper "On Koszul Algebras and a New Construction of Artin-Schelter Regular Algebras" by Shelton and Tingey

AlgebraExample3point1:= function( K ) 	#This algebra is also in Theorem 5.1.12 of cocycle-twists.pdf
	local kQ, p, rels, x1, x2, x3, x4, I, gb, A;
	kQ:= FreeKAlgebraNoGeneratorNames( GaussianRationals, 4, "x" );
	p:= E(4);
	x1:= kQ.x1; x2:= kQ.x2; x3:= kQ.x3; x4:= kQ.x4;
	rels:= [ ];
	rels[1]:= x3*x1 - x1*x3 + x2^2 ;
	rels[2]:= p*x4*x1 + x1*x4 ;
	rels[3]:= x4*x2 - x2*x4 + x3^2 ;
	rels[4]:= p*x3*x2 + x2*x3 ;
	rels[5]:= x1^2 - x3^2 ;
	rels[6]:= x2^2 - x4^2 ;
	# I:= Ideal( kQ, rels );
	# gb:= GroebnerBasis( I, rels );
	A:= kQ/rels ;
	# A:= GBQuotient( kQ, rels );
	return [ A, kQ, rels ];
end;



AlgebraExample3point1Proof:= function( K, f, a ) #f and are nonzero elements of K
	local kQ, p, rels, B, x1, x2, x3, x4, I, gb, A;
	kQ:= FreeKAlgebraNoGeneratorNames( GaussianRationals, 4, "x" );
	p:= E(4);
	x1:= kQ.x1; x2:= kQ.x2; x3:= kQ.x3; x4:= kQ.x4;
	rels:= [ ];
	rels[1]:= x2*x1 - a*x1*x2 ;
	rels[2]:= x3*x1 + x1*x3 ;
	rels[3]:= x4*x1 - p*x1*x4 ;
	rels[4]:= x3*x2 - p*x2*x3 ;
	rels[5]:= x4*x2 + x2*x4 ;
	rels[6]:= x4*x3 - f*x3*x4 ;
	# I:= Ideal( kQ, rels );
	# gb:= GroebnerBasis( I, rels );
	A:= kQ/rels ;
	# A:= GBQuotient( kQ, rels );
	return [ A, kQ, rels ];
end;



#################################################################################################################################################################################

#The next algebras are taken from the paper "Poisson Structures and Lie Algebroids in Complex Geometry", by Brent Pym

AlgebraL112:= function( K, p0, p1, lambda )	#p0 and p1 nonzero scalars in K, lambda in K
	local kQ, rels, x1, x2, x3, x4, I, gb, A ;
	kQ:= FreeKAlgebra( K, 4, "x" ) ;
	x1:= kQ.x1; x2:= kQ.x2; x3:= kQ.x3; x4:= kQ.x4;
	rels:= [ ] ;
	rels[1]:= x2*x1 - x1*x2 ;
	rels[2]:= x3*x1 - (1/p0)*x1*x3 ;
	rels[3]:= x4*x1 - p0*x1*x4 ;
	rels[4]:= x3*x2 - p1*x2*x3 ;
	rels[5]:= x4*x2 - (1/p1)*x2*x4 ;
	rels[6]:= x4*x3 - p1*(1/p0)*x3*x4 - (p1 - p0)*(x1^2 + lambda*x1*x2 + x2^2) - (1 - p0^2)*x1^2 - (p1^2 - 1)*x2^2 ;
#	I:= Ideal( kQ, rels );
#	gb:= GroebnerBasis( I, rels );
	A:= kQ/rels ;
#	A:= GBQuotient( kQ, rels );
	return [ A, kQ, rels ];
end;



AlgebraE3:= function( )
	local kQ, rels, x0, x1, x2, x3, x4, I, gb, A ;
	kQ:= FreeKAlgebra( Rationals, 4, "y" ) ;
	x0:= kQ.y1; x1:= kQ.y2; x2:= kQ.y3; x3:= kQ.y4;
	rels:= [ ] ;
	rels[1]:= Commutator( x0, x1 ) - 5*x0^2 ;
	rels[2]:= Commutator( x1, x2 ) - 3*x0*x2 - x1^2 + (3/2)*x0*x1 ;
	rels[3]:= Commutator( x0, x2 ) - 5*x0*x1 + (45/2)*x0^2 ;
	rels[4]:= Commutator( x1, x3 ) - 7*x0*x3 - x1*x2 + 3*x0*x2 + (5/2)*x1^2 - 5*x0*x1 ;
	rels[5]:= Commutator( x0, x3 ) - 5*x0*x2  + (45/2)*x0*x1 - (195/2)*x0^2 ;
	rels[6]:= Commutator( x2, x3 ) - 7*x1*x3 + (77/2)*x0*x3 + 3*x2^2 - (21/2)*x1*x2 + (77/2)*x0*x2 ;
#	I:= Ideal( kQ, rels );
#	gb:= GroebnerBasis( I, rels );
	A:= kQ/rels ;
#	A:= GBQuotient( kQ, rels );
	return [ A, kQ, rels ];
	end;



#################################################################################################################################################################################

#The next algebras are taken from the paper "NEW AS-REGULAR ALGEBRAS VIA NORMAL EXTENSIONS", by Chirvasitu, Kanda and Paul Smith


#################################################################################################################################################################################

#The next algebras are taken from the paper "Graded Algebras Of Global Dimension 3", by Artin and Schelter
