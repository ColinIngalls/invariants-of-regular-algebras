

ParameterizedAlgebraA:= function( K )
	local PolyRing, h, kQ, rels, A, I, x1, x2, x3, x4;
  PolyRing:= FunctionField( K, [ "h" ] );
  h:= IndeterminatesOfFunctionField( PolyRing )[1] ;
	kQ:= FreeKAlgebraNoGeneratorNames( PolyRing, 4, "x" );
	rels:= [ ];
	rels[1]:= kQ.x1*kQ.x2 - kQ.x2*kQ.x1 ;
	rels[2]:= kQ.x4*kQ.x3 - kQ.x3*kQ.x4 - kQ.x3^2 ;
  #
	rels[3]:= kQ.x3*kQ.x1 - h*kQ.x1*kQ.x3 ;
	rels[4]:= kQ.x3*kQ.x2 - h*(kQ.x1*kQ.x4 + kQ.x2*kQ.x3) ;
	rels[5]:= kQ.x4*kQ.x1 - h*kQ.x1*kQ.x4 ;
	rels[6]:= kQ.x4*kQ.x2 + h*((2)*kQ.x2*kQ.x3 + kQ.x1*kQ.x4 - kQ.x2*kQ.x4) ;
	A:= GBQuotient( kQ, rels );
	return [ A, kQ, rels ];
end;



ParameterizedAlgebraB:= function() #Need p^2 = -1 in K. For instance, K = Z_101 and p = 10
  local PolyRing, h, kQ, rels, B, p, I, x1, x2, x3, x4;
  PolyRing:= FunctionField( GaussianRationals, [ "h" ] );
  h:= IndeterminatesOfFunctionField( PolyRing )[1] ;
	kQ:= FreeKAlgebraNoGeneratorNames( PolyRing, 4, "x" );
	p:= E(4);
	rels:= [];
	rels[1]:= kQ.x2*kQ.x1 - (p*One(PolyRing))*kQ.x1*kQ.x2 ;
	rels[2]:= kQ.x4*kQ.x3 - (p*One(PolyRing))*kQ.x3*kQ.x4 ;
#
	rels[3]:= kQ.x3*kQ.x1 + h*(-kQ.x2*kQ.x4) ;
	rels[4]:= kQ.x3*kQ.x2 + h*(-kQ.x1*kQ.x4) ;
	rels[5]:= kQ.x4*kQ.x1 + h*(kQ.x2*kQ.x3) ;
	rels[6]:= kQ.x4*kQ.x2 + h*(-kQ.x1*kQ.x3) ;
	B:= GBQuotient( kQ, rels );
	return [ B, kQ, rels ];
end;



ParameterizedAlgebraC:= function() #p^2 + p + 1 = 0, for instance, K = Z_601 and p = 24
	local PolyRing, Qadj, h, kQ, p, rels, C, x1, x2, x3, x4;
	Qadj:= CF(Rationals, 3);
  PolyRing:= FunctionField( Qadj, [ "h" ] );
  p:= E(3)*One(PolyRing) ;
  h:= IndeterminatesOfFunctionField( PolyRing )[1] ;
	kQ:= FreeKAlgebra( PolyRing, 4, "x" );
	rels:= [];
	rels[1]:= kQ.x4*kQ.x3 - p*kQ.x3*kQ.x4 ;
	rels[2]:= kQ.x2*kQ.x1 - p*kQ.x1*kQ.x2 ;
#
	rels[3]:= kQ.x3*kQ.x1 + h*(kQ.x1*kQ.x3 - (p^2)*kQ.x2*kQ.x3 - kQ.x1*kQ.x4 + p*kQ.x2*kQ.x4) ;
	rels[4]:= kQ.x3*kQ.x2 + h*(p*kQ.x1*kQ.x3 - kQ.x2*kQ.x3 - kQ.x1*kQ.x4 + p*kQ.x2*kQ.x4) ;
	rels[5]:= kQ.x4*kQ.x1 + h*(p*kQ.x1*kQ.x3 + 2*(p^2)*kQ.x2*kQ.x3 - p*kQ.x1*kQ.x4 + p*kQ.x2*kQ.x4) ;
	rels[6]:= kQ.x4*kQ.x2 + h*(p*kQ.x1*kQ.x3 - (p^2)*kQ.x2*kQ.x3 - kQ.x1*kQ.x4 + kQ.x2*kQ.x4) ;
	C:= GBQuotient( kQ, rels );
	return [ C, kQ, rels ];
end;



ParameterizedAlgebraD:= function( K )
	local PolyRing, kQ, rels, D, p, h, x1, x2, x3, x4;
  PolyRing:= FunctionField( K, [ "p", "h" ] );
  p:= IndeterminatesOfFunctionField( PolyRing )[1] ;
  h:= IndeterminatesOfFunctionField( PolyRing )[2] ;
  kQ:= FreeKAlgebraNoGeneratorNames( PolyRing, 4, "x" );
#    p:= p*One(PolyRing);
	rels:= [];
	rels[1]:= kQ.x1*kQ.x2 + kQ.x2*kQ.x1 ;
	rels[2]:= kQ.x4*kQ.x3 - p*kQ.x3*kQ.x4 ;
#
	rels[3]:= kQ.x3*kQ.x1 + h*(p*kQ.x1*kQ.x3) ;
	rels[4]:= kQ.x3*kQ.x2 + h*((p*p)*kQ.x2*kQ.x3 - kQ.x1*kQ.x4) ;
	rels[5]:= kQ.x4*kQ.x1 - h*(p*kQ.x1*kQ.x4) ;
	rels[6]:= kQ.x4*kQ.x2 + h*(-kQ.x1*kQ.x3 - kQ.x2*kQ.x4) ;
#	D:= GBQuotient( kQ, rels );
	return [ 0, kQ, rels ];
end;



ParameterizedAlgebraE:= function( )
	local PolyRing, h, kQ, p, rels, C, x1, x2, x3, x4, Ee;
  PolyRing:= FunctionField( GaussianRationals, [ "h" ] );
  h:= IndeterminatesOfFunctionField( PolyRing )[1] ;
	kQ:= FreeKAlgebraNoGeneratorNames( PolyRing, 4, "x" );
	p:= E(4)*One(PolyRing) ;
	rels:= [];
	rels[1]:= kQ.x2*kQ.x1 + kQ.x1*kQ.x2 ;
	rels[2]:= kQ.x4*kQ.x3 - p*kQ.x3*kQ.x4 ;
#
	rels[3]:= kQ.x3*kQ.x1 + h*(-kQ.x1*kQ.x4 - kQ.x2*kQ.x4 ) ;
	rels[4]:= kQ.x3*kQ.x2 + h*(-kQ.x1*kQ.x4 + kQ.x2*kQ.x4 ) ;
	rels[5]:= kQ.x4*kQ.x1 + h*(kQ.x1*kQ.x3 - kQ.x2*kQ.x3 ) ;
	rels[6]:= kQ.x4*kQ.x2 + h*(-kQ.x1*kQ.x3 - kQ.x2*kQ.x3 ) ;
	Ee:= GBQuotient( kQ, rels );
	return [ Ee, kQ, rels ];
end;



ParameterizedAlgebraF:= function( )
	local PolyRing, h, kQ, p, rels, F, x1, x2, x3, x4;
  PolyRing:= FunctionField( GaussianRationals, [ "h" ] );
  h:= IndeterminatesOfFunctionField( PolyRing )[1] ;
	kQ:= FreeKAlgebraNoGeneratorNames( PolyRing, 4, "x" );
	p:= E(4)*One( PolyRing );
	rels:= [ ];
	rels[1]:= kQ.x2*kQ.x1 + kQ.x1*kQ.x2 ;
	rels[2]:= kQ.x4*kQ.x3 - p*kQ.x3*kQ.x4 ;
#
	rels[3]:= kQ.x3*kQ.x1 + h*(kQ.x1*kQ.x3 + p*kQ.x2*kQ.x3 - kQ.x1*kQ.x4 + kQ.x2*kQ.x4) ;
	rels[4]:= kQ.x3*kQ.x2 + h*(p*kQ.x1*kQ.x3 - kQ.x2*kQ.x3 - kQ.x1*kQ.x4 - kQ.x2*kQ.x4 );
	rels[5]:= kQ.x4*kQ.x1 + h*(p*kQ.x1*kQ.x3 - p*kQ.x2*kQ.x3 - p*kQ.x1*kQ.x4 - kQ.x2*kQ.x4) ;
	rels[6]:= kQ.x4*kQ.x2 + h*(p*kQ.x1*kQ.x3 + p*kQ.x2*kQ.x3 - kQ.x1*kQ.x4 + p*kQ.x2*kQ.x4) ;
	F:= GBQuotient( kQ, rels );
	return [ F, kQ, rels ];
end;



ParameterizedAlgebraG:= function( K )
	local PolyRing, p, f, h, kQ, rels, G, x1, x2, x3, x4;
  PolyRing:= FunctionField( K, [ "p", "f", "h" ] );
  p:= IndeterminatesOfFunctionField( PolyRing )[1];
  f:= IndeterminatesOfFunctionField( PolyRing )[2];
  h:= IndeterminatesOfFunctionField( PolyRing )[3];
	kQ:= FreeKAlgebra( PolyRing, 4, "x" );
	rels:= [];
	rels[1]:= kQ.x2*kQ.x1 - kQ.x1*kQ.x2 ;
	rels[2]:= kQ.x4*kQ.x3 - p*kQ.x3*kQ.x4 ;
#
	rels[3]:= kQ.x3*kQ.x1 + h*(-p*kQ.x1*kQ.x3) ;
	rels[4]:= kQ.x3*kQ.x2 + h*(-p*kQ.x1*kQ.x3 - (p*p)*kQ.x2*kQ.x3 - kQ.x1*kQ.x4);
	rels[5]:= kQ.x4*kQ.x1 + h*(-p*kQ.x1*kQ.x4) ;
	rels[6]:= kQ.x4*kQ.x2 + h*(-f*kQ.x1*kQ.x3 + kQ.x1*kQ.x4 - kQ.x2*kQ.x4 );
	G:= GBQuotient( kQ, rels );
	return [G, kQ, rels] ;
end;



ParameterizedAlgebraH:= function( K )
	local PolyRing, kQ, rels, f, h, x1, x2, x3, x4, I, gb, A ;
  PolyRing:= FunctionField( K, [ "f", "h" ] );
  f:= IndeterminatesOfFunctionField( PolyRing )[1];
  h:= IndeterminatesOfFunctionField( PolyRing )[2];
	kQ:= FreeKAlgebra( PolyRing, 4, "x" );
	x1:= kQ.x1; x2:= kQ.x2; x3:= kQ.x3; x4:= kQ.x4;
	rels:= [];
	rels[1]:= x2*x1 - x1*x2 - x1^2 ;
	rels[2]:= x4*x3 + x3*x4 ;
#
	rels[3]:= x3*x1 - h*x1*x4 ;
	rels[4]:= x3*x2 - h*f*x1*x4 - h*x2*x4 ;
	rels[5]:= x4*x1 - h*x1*x3 ;
	rels[6]:= x4*x2 - h*f*x1*x3 - h*x2*x3 ;
	#	I:= Ideal( kQ, rels );
	#	gb:= GroebnerBasis( I, rels );
	A:= kQ/rels ;
	#	A:= GBQuotient( kQ, rels );
	return [ A, kQ, rels ] ;
end;



ParameterizedAlgebraI:= function( )   #Need to find a way to encode q^2 = -1 # Use the function FieldExtension
	local PolyRing, h, kQ, rels, q, I, J, x1, x2, x3, x4;
  PolyRing:= FunctionField( GaussianRationals, [ "t1" ] );
  h:= IndeterminatesOfFunctionField( PolyRing )[1] ;
  kQ:= FreeKAlgebraNoGeneratorNames( PolyRing, 4, "x" );
  q:= E(4)*One( PolyRing );
	rels:= [ ];
	rels[1]:= kQ.x2*kQ.x1 - q*kQ.x1*kQ.x2 ;
	rels[2]:= kQ.x4*kQ.x3 + kQ.x3*kQ.x4 ;
#
	rels[3]:= kQ.x3*kQ.x1 + h*(q*kQ.x1*kQ.x3 + q*kQ.x2*kQ.x3 - kQ.x1*kQ.x4 + q*kQ.x2*kQ.x4 ) ;
	rels[4]:= kQ.x3*kQ.x2 + h*(-kQ.x1*kQ.x3 - kQ.x2*kQ.x3 - kQ.x1*kQ.x4 + q*kQ.x2*kQ.x4 ) ;
	rels[5]:= kQ.x4*kQ.x1 + h*( -kQ.x1*kQ.x3 - q*kQ.x2*kQ.x3 - q*kQ.x1*kQ.x4 + q*kQ.x2*kQ.x4 ) ;
	rels[6]:= kQ.x4*kQ.x2 + h*(kQ.x1*kQ.x3 + q*kQ.x2*kQ.x3 - kQ.x1 * kQ.x4 + kQ.x2*kQ.x4 ) ;
#	J:= Ideal( kQ, rels );
	I:= GBQuotient( kQ, rels );
	return [I, kQ, rels ];
end;



ParameterizedAlgebraJ:= function( )
  local PolyRing, h, kQ, rels, q, I, J, x1, x2, x3, x4;
  PolyRing:= FunctionField( GaussianRationals, [ "h" ] );
  h:= IndeterminatesOfFunctionField( PolyRing )[1] ;
  kQ:= FreeKAlgebraNoGeneratorNames( PolyRing, 4, "x" );
  q:= E(4)*One( PolyRing );
	rels:= [];
	rels[1]:= kQ.x2*kQ.x1 - q*kQ.x1*kQ.x2 ;
	rels[2]:= kQ.x4*kQ.x3 + kQ.x3*kQ.x4 ;
#
	rels[3]:= kQ.x3*kQ.x1 + h*(-kQ.x2*kQ.x3 - kQ.x2*kQ.x4 ) ;
	rels[4]:= kQ.x3*kQ.x2 + h*(kQ.x1*kQ.x3 - kQ.x1*kQ.x4 ) ;
	rels[5]:= kQ.x4*kQ.x1 + h*(-kQ.x2*kQ.x3 + kQ.x2*kQ.x4 ) ;
	rels[6]:= kQ.x4*kQ.x2 + h*(-kQ.x1*kQ.x3 - kQ.x1*kQ.x4 ) ;
	J:= GBQuotient( kQ, rels );
	return [ J, kQ, rels ];
end;



#ParameterizedAlgebraK:= function( K, q ) #q = 1 or q = -1
#	local PolyRing, t1, t2, PolyQ, rels, KAlg, x1, x2, x3, x4;
#  PolyRing:= FunctionField( K, [ "t1", "t2" ] );
#  t1:= IndeterminatesOfFunctionField( PolyRing )[1];
#  t2:= IndeterminatesOfFunctionField( PolyRing )[2];
#	PolyQ:= FreeKAlgebra( PolyRing, 4, "x" );
#	rels:= [];
#	rels[1]:= PolyQ.x2*PolyQ.x1 - q*PolyQ.x1*PolyQ.x2 ;
#	rels[2]:= PolyQ.x4*PolyQ.x3 + PolyQ.x3*PolyQ.x4 ;
#
#	rels[3]:= PolyQ.x3*PolyQ.x1 - t2*(PolyQ.x1*PolyQ.x3) ;
#	rels[4]:= PolyQ.x3*PolyQ.x2 - t2*(PolyQ.x2*PolyQ.x4) ;
#	rels[5]:= PolyQ.x4*PolyQ.x1 - t2*(PolyQ.x1*PolyQ.x4) ;
#	rels[6]:= PolyQ.x4*PolyQ.x2 - t2*(t1*PolyQ.x2*PolyQ.x3) ;
#	KAlg:= GBQuotient( PolyQ, rels );
#	return [ KAlg, PolyQ, rels ];
#end;



ParameterizedAlgebraK:= function( K )
	local PolyRing, h, f, q, kQ, rels, KAlg, x1, x2, x3, x4;
  PolyRing:= FunctionField( K, [ "f", "q", "h" ] );
  f:= IndeterminatesOfFunctionField( PolyRing )[1];
  q:= IndeterminatesOfFunctionField( PolyRing )[2];
  h:= IndeterminatesOfFunctionField( PolyRing )[3];
	kQ:= FreeKAlgebraNoGeneratorNames( PolyRing, 4, "x" );
	rels:= [];
	rels[1]:= kQ.x2*kQ.x1 - q*kQ.x1*kQ.x2 ;
	rels[2]:= kQ.x4*kQ.x3 + kQ.x3*kQ.x4 ;
#
	rels[3]:= kQ.x3*kQ.x1 + h*(-kQ.x1*kQ.x3) ;
	rels[4]:= kQ.x3*kQ.x2 + h*(-kQ.x2*kQ.x4) ;
	rels[5]:= kQ.x4*kQ.x1 + h*(-kQ.x1*kQ.x4) ;
	rels[6]:= kQ.x4*kQ.x2 + h*(-f*kQ.x2*kQ.x3) ;
	KAlg:= GBQuotient( kQ, rels );
	return [ KAlg, kQ, rels ];
end;



#ParameterizedAlgebraL:= function( K, q) #q = 1 or q = -1
#  local PolyRing, t1, t2, kQ, rels, L, x1, x2, x3, x4;
#  PolyRing:= FunctionField( K, [ "t1", "t2" ] );
#  t1:= IndeterminatesOfFunctionField( PolyRing )[1];
#  t2:= IndeterminatesOfFunctionField( PolyRing )[2];
#	kQ:= FreeKAlgebra( PolyRing, 4, "x" );;
#	rels:= [];
#  if q = 1 or q = -1 then
#    rels[1]:= kQ.x2*kQ.x1 - q*kQ.x1*kQ.x2 ;
#    rels[2]:= kQ.x4*kQ.x3 + kQ.x3*kQ.x4 ;
#
#    rels[3]:= kQ.x3*kQ.x1 - t2*t1*kQ.x1*kQ.x4 ;
#    rels[4]:= kQ.x3*kQ.x2 - t2*kQ.x2*kQ.x4 ;
#    rels[5]:= kQ.x4*kQ.x1 - t2*t1*kQ.x1*kQ.x3 ;
#    rels[6]:= kQ.x4*kQ.x2 - t2*kQ.x2*kQ.x3 ;
#    L:= GBQuotient( kQ, rels );
#    return [ L, kQ, rels ];
#  else
#		Error("f needs to be nonzero, and q can only be 1 or -1");
#	fi;
#end;




ParameterizedAlgebraL:= function( K )
  local PolyRing, f, q, h, kQ, rels, L, x1, x2, x3, x4;
  PolyRing:= FunctionField( K, [ "f", "q", "h" ] );
  f:= IndeterminatesOfFunctionField( PolyRing )[1];
  q:= IndeterminatesOfFunctionField( PolyRing )[2];
  h:= IndeterminatesOfFunctionField( PolyRing )[3];
	kQ:= FreeKAlgebraNoGeneratorNames( PolyRing, 4, "x" );
	rels:= [];
	rels[1]:= kQ.x2*kQ.x1 - q*kQ.x1*kQ.x2 ;
	rels[2]:= kQ.x4*kQ.x3 + kQ.x3*kQ.x4 ;
#
	rels[3]:= kQ.x3*kQ.x1 + h*(-f*kQ.x1*kQ.x4) ;
	rels[4]:= kQ.x3*kQ.x2 + h*(-kQ.x2*kQ.x4) ;
	rels[5]:= kQ.x4*kQ.x1 + h*(-f*kQ.x1*kQ.x3) ;
	rels[6]:= kQ.x4*kQ.x2 + h*(-kQ.x2*kQ.x3) ;
	L:= GBQuotient( kQ, rels );
	return [ L, kQ, rels ];
end;



ParameterizedAlgebraM:= function( K )
  local PolyRing, kQ, rels, M, f, h, x1, x2, x3, x4;
  PolyRing:= FunctionField( K, [ "f", "h" ] );
  f:= IndeterminatesOfFunctionField( PolyRing )[1] ;
  h:= IndeterminatesOfFunctionField( PolyRing )[2] ;
	kQ:= FreeKAlgebraNoGeneratorNames( PolyRing, 4, "x" );
	rels:= [];
	rels[1]:= kQ.x2*kQ.x1 + kQ.x1*kQ.x2 ;
	rels[2]:= kQ.x4*kQ.x3 + kQ.x3*kQ.x4 ;
#
	rels[3]:= kQ.x3*kQ.x1 + h*(-kQ.x2*kQ.x3 - kQ.x1*kQ.x4 ) ;
	rels[4]:= kQ.x3*kQ.x2 + h*(-f*kQ.x1*kQ.x3 + kQ.x2*kQ.x4 ) ;
	rels[5]:= kQ.x4*kQ.x1 + h*(-kQ.x1*kQ.x3 + kQ.x2*kQ.x4 ) ;
	rels[6]:= kQ.x4*kQ.x2 + h*(kQ.x2*kQ.x3 + f*kQ.x1*kQ.x4 ) ;
	M:= GBQuotient( kQ, rels );
	return [ M, kQ, rels ];
end;



ParameterizedAlgebraN:= function( K ) #Do not evaluate at a point where t1^2 = t2^2
  local PolyRing, f, g, h, kQ, rels, N, x1, x2, x3, x4;
  PolyRing:= FunctionField( K, [ "f", "g", "h" ] );
  f:= IndeterminatesOfFunctionField( PolyRing )[1];
  g:= IndeterminatesOfFunctionField( PolyRing )[2];
  h:= IndeterminatesOfFunctionField( PolyRing )[3];
	kQ:= FreeKAlgebra( PolyRing, 4, "x" );;
	rels:= [];
	rels[1]:= kQ.x2*kQ.x1 + kQ.x1*kQ.x2 ;
	rels[2]:= kQ.x4*kQ.x3 + kQ.x3*kQ.x4 ;
#
	rels[3]:= kQ.x3*kQ.x1 + h*(g*kQ.x2*kQ.x3 - f*kQ.x2*kQ.x4 ) ;
	rels[4]:= kQ.x3*kQ.x2 + h*(-g*kQ.x1*kQ.x3 - f*kQ.x1*kQ.x4 ) ;
	rels[5]:= kQ.x4*kQ.x1 + h*(-f*kQ.x2*kQ.x3 + g*kQ.x2*kQ.x4 ) ;
	rels[6]:= kQ.x4*kQ.x2 + h*(-f*kQ.x1*kQ.x3 - g*kQ.x1*kQ.x4 ) ;
	N:= GBQuotient( kQ, rels );
	return [ N, kQ, rels ];
end;



ParameterizedAlgebraO:= function( K ) #Do not evaluate at t1 = 1
  local PolyRing, f, h, kQ, rels, O, x1, x2, x3, x4;
  PolyRing:= FunctionField( K, [ "f", "h" ] );
  f:= IndeterminatesOfFunctionField( PolyRing )[1];
  h:= IndeterminatesOfFunctionField( PolyRing )[2];
	kQ:= FreeKAlgebra( PolyRing, 4, "x" );;
	rels:= [ ];
	rels[1]:= kQ.x2*kQ.x1 + kQ.x1*kQ.x2 ;
	rels[2]:= kQ.x4*kQ.x3 + kQ.x3*kQ.x4 ;
#
	rels[3]:= kQ.x3*kQ.x1 + h*(-kQ.x1*kQ.x3 - f*kQ.x2*kQ.x4 ) ;
	rels[4]:= kQ.x3*kQ.x2 + h*(kQ.x2*kQ.x3 - kQ.x1*kQ.x4 ) ;
	rels[5]:= kQ.x4*kQ.x1 + h*(-f*kQ.x2*kQ.x3 + kQ.x1*kQ.x4 ) ;
	rels[6]:= kQ.x4*kQ.x2 + h*(-kQ.x1*kQ.x3 - kQ.x2*kQ.x4 ) ;
	O:= GBQuotient( kQ, rels );
	return [ O, kQ, rels ];
end;



ParameterizedAlgebraP:= function( K ) #Check for t1 cannot be 1
  local PolyRing, f, h, kQ, rels, Palg, x1, x2, x3, x4;
  PolyRing:= FunctionField( K, [ "f", "h" ] );
  f:= IndeterminatesOfFunctionField( PolyRing )[1];
  h:= IndeterminatesOfFunctionField( PolyRing )[2];
  kQ:= FreeKAlgebra( PolyRing, 4, "x" );;
	rels:= [ ];
	rels[1]:= kQ.x2*kQ.x1 + kQ.x1*kQ.x2 ;
	rels[2]:= kQ.x4*kQ.x3 + kQ.x3*kQ.x4 ;
#
	rels[3]:= kQ.x3*kQ.x1 + h*(-kQ.x1*kQ.x4 - f*kQ.x2*kQ.x4 ) ;
	rels[4]:= kQ.x3*kQ.x2 + h*(-kQ.x1*kQ.x4 - kQ.x2*kQ.x4 ) ;
	rels[5]:= kQ.x4*kQ.x1 + h*(-kQ.x1*kQ.x3 + f*kQ.x2*kQ.x3 ) ;
	rels[6]:= kQ.x4*kQ.x2 + h*(kQ.x1*kQ.x3 - kQ.x2*kQ.x3 ) ;
	Palg:= GBQuotient( kQ, rels );
	return [ Palg, kQ, rels ];
end;



ParameterizedAlgebraQ:= function( K )
  local PolyRing, h, kQ, rels, Q, x1, x2, x3, x4;
  PolyRing:= FunctionField( K, [ "h" ] );
  h:= IndeterminatesOfFunctionField( PolyRing )[1];
  kQ:= FreeKAlgebra( PolyRing, 4, "x" );;
	rels:= [ ];
	rels[1]:= kQ.x2*kQ.x1 + kQ.x1*kQ.x2 ;
	rels[2]:= kQ.x4*kQ.x3 + kQ.x3*kQ.x4 ;
#
	rels[3]:= kQ.x3*kQ.x1 + h*(-kQ.x1*kQ.x4) ;
	rels[4]:= kQ.x3*kQ.x2 + h*(-kQ.x1*kQ.x3 - kQ.x2*kQ.x3 - kQ.x1*kQ.x4 ) ;
	rels[5]:= kQ.x4*kQ.x1 + h*(kQ.x1*kQ.x3 ) ;
	rels[6]:= kQ.x4*kQ.x2 + h*(-kQ.x1*kQ.x3 + kQ.x1*kQ.x4 - kQ.x2*kQ.x4 ) ;
	Q:= GBQuotient( kQ, rels );
	return [ Q, kQ, rels ];
end;



ParameterizedAlgebraR:= function( K )
  local PolyRing, h, kQ, rels, R, x1, x2, x3, x4;
  PolyRing:= FunctionField( K, [ "h" ] );
  h:= IndeterminatesOfFunctionField( PolyRing )[1];
  kQ:= FreeKAlgebra( PolyRing, 4, "x" );;
	rels:= [ ];
	rels[1]:= kQ.x2*kQ.x1 + kQ.x1*kQ.x2 ;
	rels[2]:= kQ.x4*kQ.x3 + kQ.x3*kQ.x4 ;
#
	rels[3]:= kQ.x3*kQ.x1 + h*(-kQ.x1*kQ.x3 - kQ.x2*kQ.x3 - kQ.x1*kQ.x4 ) ;
	rels[4]:= kQ.x3*kQ.x2 + h*(-kQ.x1*kQ.x4 ) ;
	rels[5]:= kQ.x4*kQ.x1 + h*(-kQ.x2*kQ.x3 ) ;
	rels[6]:= kQ.x4*kQ.x2 + h*(kQ.x2*kQ.x3 + kQ.x1*kQ.x4 - kQ.x2*kQ.x4 );
	R:= GBQuotient( kQ, rels );
	return [ R, kQ, rels ];
end;



ParameterizedAlgebraS:= function( K )
	local PolyRing, h, kQ, rels, x1, x2, x3, x4, I, gb, A ;
  PolyRing:= FunctionField( K, [ "h" ] );
  h:= IndeterminatesOfFunctionField( PolyRing )[1];
  kQ:= FreeKAlgebra( PolyRing, 4, "x" );
	x1:= kQ.x1; x2:= kQ.x2; x3:= kQ.x3; x4:= kQ.x4;
	rels:= [];
	rels[1]:= x2*x1 + x1*x2 ;
	rels[2]:= x4*x3 + x3*x4 ;
#
	rels[3]:= x3*x1 + h*(x1*x3 - x2*x3 - x1*x4 - x2*x4 ) ;
	rels[4]:= x3*x2 + h*(-x1*x3 + x2*x3 - x1*x4 - x2*x4 ) ;
	rels[5]:= x4*x1 + h*(-x1*x3 - x2*x3 + x1*x4 - x2*x4 ) ;
	rels[6]:= x4*x2 + h*(-x1*x3 - x2*x3 - x1*x4 + x2*x4 ) ;
	#	I:= Ideal( kQ, rels );
	#	gb:= GroebnerBasis( I, rels );
	A:= kQ/rels ;
	#	A:= GBQuotient( kQ, rels );
	return [ A, kQ, rels ] ;
end;



ParameterizedAlgebraT:= function( K )
  local PolyRing, h, kQ, rels, T, x1, x2, x3, x4;
  PolyRing:= FunctionField( K, [ "h" ] );
  h:= IndeterminatesOfFunctionField( PolyRing )[1];
  kQ:= FreeKAlgebra( PolyRing, 4, "x" );
	rels:= [];
	rels[1]:= kQ.x2*kQ.x1 + kQ.x1*kQ.x2 ;
	rels[2]:= kQ.x4*kQ.x3 + kQ.x3*kQ.x4 ;
#
	rels[3]:= kQ.x3*kQ.x1 + h*(kQ.x1*kQ.x3 - kQ.x2*kQ.x3 - kQ.x1*kQ.x4 - kQ.x2*kQ.x4 ) ;
	rels[4]:= kQ.x3*kQ.x2 + h*(-kQ.x1*kQ.x3 + kQ.x2*kQ.x3 - kQ.x1*kQ.x4 - kQ.x2*kQ.x4 ) ;
	rels[5]:= kQ.x4*kQ.x1 + h*(-kQ.x1*kQ.x3 - kQ.x2*kQ.x3 - kQ.x1*kQ.x4 + kQ.x2*kQ.x4 ) ;
	rels[6]:= kQ.x4*kQ.x2 + h*(-kQ.x1*kQ.x3 - kQ.x2*kQ.x3 + kQ.x1*kQ.x4 - kQ.x2*kQ.x4 ) ;
	T:= GBQuotient( kQ, rels );
	return [ T, kQ, rels ];
end;



ParameterizedAlgebraU:= function( K )
  local PolyRing, h, kQ, rels, x1, x2, x3, x4, I, gb, A ;
  PolyRing:= FunctionField( K, [ "h" ] );
  h:= IndeterminatesOfFunctionField( PolyRing )[1];
  kQ:= FreeKAlgebra( PolyRing, 4, "x" );
	x1:= kQ.x1; x2:= kQ.x2; x3:= kQ.x3; x4:= kQ.x4;
	rels:= [];
	rels[1]:= x2*x1 + x1*x2 ;
	rels[2]:= x4*x3 + x3*x4 ;
#
	rels[3]:= x3*x1 + h*(x1*x3 - x2*x3 - x1*x4 - x2*x4 ) ;
	rels[4]:= x3*x2 + h*(-x1*x3 - x2*x3 - x1*x4 + x2*x4 ) ;
	rels[5]:= x4*x1 + h*(-x1*x3 - x2*x3 + x1*x4 - x2*x4 ) ;
	rels[6]:= x4*x2 + h*(-x1*x3 + x2*x3 - x1*x4 - x2*x4 ) ;
	#	I:= Ideal( kQ, rels );
	#	gb:= GroebnerBasis( I, rels );
	A:= kQ/rels ;
	#	A:= GBQuotient( kQ, rels );
	return [ A, kQ, rels ] ;
end;


ParameterizedAlgebraV:= function( K )
  local PolyRing, h, kQ, rels, x1, x2, x3, x4, I, gb, A ;
  PolyRing:= FunctionField( K, [ "h" ] );
  h:= IndeterminatesOfFunctionField( PolyRing )[1];
  kQ:= FreeKAlgebra( PolyRing, 4, "x" );
	x1:= kQ.x1; x2:= kQ.x2; x3:= kQ.x3; x4:= kQ.x4;
	rels:= [];
	rels[1]:= x2*x1 - x1*x2 ;
	rels[2]:= x4*x3 + x3*x4 ;
#
	rels[3]:= x3*x1 + h*(-x2*x3 - x1*x4 ) ;
	rels[4]:= x3*x2 - h*x2*x3 ;
	rels[5]:= x4*x1 + h*(x1*x3 - x2*x3 ) ;
	rels[6]:= x4*x2 - h*x2*x4 ;
	#	I:= Ideal( kQ, rels );
	#	gb:= GroebnerBasis( I, rels );
	A:= kQ/rels ;
	#	A:= GBQuotient( kQ, rels );
	return [ A, kQ, rels ] ;
end;


ParameterizedAlgebraW:= function( K ) #f \neq -1
  local PolyRing, f, h, kQ, rels, x1, x2, x3, x4, I, gb, A ;
  PolyRing:= FunctionField( K, [ "f", "h" ] );
  f:= IndeterminatesOfFunctionField( PolyRing )[1];
  h:= IndeterminatesOfFunctionField( PolyRing )[2];
  kQ:= FreeKAlgebra( PolyRing, 4, "x" );
	x1:= kQ.x1; x2:= kQ.x2; x3:= kQ.x3; x4:= kQ.x4;
	rels:= [];
	rels[1]:= x2*x1 - x1*x2 ;
	rels[2]:= x4*x3 + x3*x4 ;
#
  rels[3]:= x3*x1 + h*(-f*x2*x3 - x1*x4 ) ;
  rels[4]:= x3*x2 + h*(-x1*x3 + x2*x4 ) ;
  rels[5]:= x4*x1 + h*(-x1*x3 - f*x2*x4 ) ;
  rels[6]:= x4*x2 + h*(x2*x3 - x1*x4 ) ;
	#	I:= Ideal( kQ, rels );
	#	gb:= GroebnerBasis( I, rels );
	A:= kQ/rels ;
	#	A:= GBQuotient( kQ, rels );
	return [ A, kQ, rels ] ;
end;


ParameterizedAlgebraX:= function( K )
  local PolyRing, h, kQ, rels, x1, x2, x3, x4, I, gb, A ;
  PolyRing:= FunctionField( K, [ "h" ] );
  h:= IndeterminatesOfFunctionField( PolyRing )[1];
  kQ:= FreeKAlgebra( PolyRing, 4, "x" );
	x1:= kQ.x1; x2:= kQ.x2; x3:= kQ.x3; x4:= kQ.x4;
	rels:= [];
	rels[1]:= x2*x1 - x1*x2 ;
	rels[2]:= x4*x3 + x3*x4 ;
#
	rels[3]:= x3*x1 + h*(-x1*x4) ;
	rels[4]:= x3*x2 + h*(-x1*x4 - x2*x4 ) ;
	rels[5]:= x4*x1 + h*(-x1*x3 ) ;
	rels[6]:= x4*x2 + h*(-x1*x3 - x2*x3 ) ;
	#	I:= Ideal( kQ, rels );
	#	gb:= GroebnerBasis( I, rels );
	A:= kQ/rels ;
	#	A:= GBQuotient( kQ, rels );
	return [ A, kQ, rels ] ;
end;


ParameterizedAlgebraY:= function( K )
  local PolyRing, f, h, kQ, rels, x1, x2, x3, x4, I, gb, A ;
  PolyRing:= FunctionField( K, [ "f", "h" ] );
  f:= IndeterminatesOfFunctionField( PolyRing )[1];
  h:= IndeterminatesOfFunctionField( PolyRing )[2];
  kQ:= FreeKAlgebra( PolyRing, 4, "x" );
	x1:= kQ.x1; x2:= kQ.x2; x3:= kQ.x3; x4:= kQ.x4;
	rels:= [];
	rels[1]:= x2*x1 - x1*x2 ;
	rels[2]:= x4*x3 + x3*x4 ;
#
	rels[3]:= x3*x1 + h*(-x1*x3) ;
	rels[4]:= x3*x2 + h*(-f*x1*x3 + x2*x3 - x1*x4 ) ;
	rels[5]:= x4*x1 + h*(-x1*x4 ) ;
	rels[6]:= x4*x2 + h*(-x1*x3 - f*x1*x4 + x2*x4 ) ;
	#	I:= Ideal( kQ, rels );
	#	gb:= GroebnerBasis( I, rels );
	A:= kQ/rels ;
	#	A:= GBQuotient( kQ, rels );
	return [ A, kQ, rels ] ;
end;




ParameterizedAlgebraZ:= function( K ) #need t1(t1+1) != 0
  local PolyRing, f, h, kQ, rels, Zalg, x1, x2, x3, x4;
  PolyRing:= FunctionField( K, [ "f", "h" ] );
  f:= IndeterminatesOfFunctionField( PolyRing )[1];
  h:= IndeterminatesOfFunctionField( PolyRing )[2];
  kQ:= FreeKAlgebra( PolyRing, 4, "x" );;
#	if f*(1+f) = 0 then
#		Print( "Need f(1+f) != 0" );
#	else
		rels:= [ ];
		rels[1]:= kQ.x2*kQ.x1 + kQ.x1*kQ.x2 ;
		rels[2]:= kQ.x4*kQ.x3 - kQ.x3*kQ.x4 ;
#
		rels[3]:= kQ.x3*kQ.x1 + h*(-kQ.x1*kQ.x3 - kQ.x2*kQ.x4 ) ;
		rels[4]:= kQ.x3*kQ.x2 + h*(-kQ.x2*kQ.x3 - kQ.x1*kQ.x4 ) ;
		rels[5]:= kQ.x4*kQ.x1 + h*(-f*kQ.x2*kQ.x3 + kQ.x1*kQ.x4 ) ;
		rels[6]:= kQ.x4*kQ.x2 + h*(-f*kQ.x1*kQ.x3 + kQ.x2*kQ.x4 ) ;
#		I:= Ideal( kQ, rels );
		Zalg:= GBQuotient( kQ, rels );
#		Zalg:= kQ/I ;
		return [ Zalg, kQ, rels ];
#	fi;
end;


####################################################################################################################################################


ParameterizedLeBruynAlgebra:= function( K )  # alphalist is a list [ alpha1, alpha2, alpha3 ]
                                            # of lists of elements of k, and SymMay is a list
																					  # of lists of elements of k representing a symmetric
																					  # 3x3 matrix. Also, we set x4 = z
	local PolyRing, indets, a, b, c, alpha1, alpha2, alpha3, l11, l12, l13, l22, l23, l33, kQ, rels, A, I, gb, x1, x2, x3, x4 ;
  PolyRing:= FunctionField( K, [ "a", "b", "c", "alpha1", "alpha2", "alpha3", "l11", "l12", "l13", "l22", "l23", "l33" ] );
  indets:= IndeterminatesOfFunctionField( PolyRing );
  a:= indets[1]; b:= indets[2]; c:= indets[3]; alpha1:= indets[4]; alpha2:= indets[5]; alpha3:= indets[6];
  l11:= indets[7]; l12:= indets[8]; l13:= indets[9]; l22:= indets[10]; l23:= indets[11]; l33:= indets[12];
  kQ:= FreeKAlgebra( PolyRing, 4, "x" );
	rels:=[];
	rels[1]:= c*kQ.x1^2 + a*kQ.x2*kQ.x3 + b*kQ.x3*kQ.x2 + l11*kQ.x1*kQ.x4 + l12*kQ.x2*kQ.x4 + l13*kQ.x3*kQ.x4 + alpha1*kQ.x4^2 ;
	rels[2]:= c*kQ.x2^2 + a*kQ.x3*kQ.x1 + b*kQ.x1*kQ.x3 + l12*kQ.x1*kQ.x4 + l22*kQ.x2*kQ.x4 + l23*kQ.x3*kQ.x4 + alpha2*kQ.x4^2 ;
	rels[3]:= c*kQ.x3^2 + a*kQ.x1*kQ.x2 + b*kQ.x2*kQ.x1 + l13*kQ.x1*kQ.x4 + l23*kQ.x2*kQ.x4 + l33*kQ.x3*kQ.x4 + alpha3*kQ.x4^2 ;
	rels[4]:= kQ.x1*kQ.x4 - kQ.x4*kQ.x1 ;
	rels[5]:= kQ.x2*kQ.x4 - kQ.x4*kQ.x2 ;
	rels[6]:= kQ.x3*kQ.x4 - kQ.x4*kQ.x3 ;
#	I:= Ideal( kQ, rels );
#	gb:= GroebnerBasis( I, rels );
#	A:= kQ/I ;
#	A:= GBQuotient( kQ, rels );
	return [ 0, kQ, rels ] ;
end;


ParameterizedLeBruynAlgebra2:= function( K )	#a, b, c are elements of k
  local PolyRing, indets, a, b, c, kQ, rels, A, I, gb, x1, x2, x3, x4 ;
  PolyRing:= FunctionField( K, [ "a", "b", "c" ] );
  indets:= IndeterminatesOfFunctionField( PolyRing );
  a:= indets[1]; b:= indets[2]; c:= indets[3];
  kQ:= FreeKAlgebra( PolyRing, 4, "x" );
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


####################################################################################################################################################

#These algebras are sources from cocycle-twists.pdf


Parameterized4dSklyaninAlgebra:= function( K )	#(1.1.16)
	local PolyRing, kQ, alpha, beta, gamma, rels, I, gb, A ;
  PolyRing:= FunctionField( K, [ "beta", "gamma" ] ) ;
  beta:= IndeterminatesOfFunctionField( PolyRing )[1] ;
  gamma:= IndeterminatesOfFunctionField( PolyRing )[2] ;
	alpha:= -(beta + gamma)/(1 + beta*gamma) ;
	kQ:= FreeKAlgebra( PolyRing, 4, "x" );
	rels:= [ ] ;
	rels[1]:= Commutator( kQ.x1, kQ.x2 ) - alpha*SkewCommutator( kQ.x3, kQ.x4 ) ;
	rels[2]:= SkewCommutator( kQ.x1, kQ.x2 ) - Commutator( kQ.x3, kQ.x4 ) ;
	rels[3]:= Commutator( kQ.x1, kQ.x3 ) - beta*SkewCommutator( kQ.x4, kQ.x2 ) ;
	rels[4]:= SkewCommutator( kQ.x1, kQ.x3 ) - Commutator( kQ.x4, kQ.x2 ) ;
	rels[5]:= Commutator( kQ.x1, kQ.x4 ) - gamma*SkewCommutator( kQ.x2, kQ.x3 ) ;
	rels[6]:= SkewCommutator( kQ.x1, kQ.x4 ) - Commutator( kQ.x2, kQ.x3 ) ;
#	I:= Ideal( kQ, rels );
#	gb:= GroebnerBasis( I, rels );
#	A:= kQ/I ;
#	A:= GBQuotient( kQ, rels );
	return [ 0, kQ, rels ];
end;



Parameterized4dSklyaninAlgebraTwist:= function( K )	#(4.1.4)
  local PolyRing, kQ, alpha, beta, gamma, rels, I, gb, A ;
  PolyRing:= FunctionField( K, [ "beta", "gamma" ] ) ;
  beta:= IndeterminatesOfFunctionField( PolyRing )[1] ;
  gamma:= IndeterminatesOfFunctionField( PolyRing )[2] ;
	alpha:= -(beta + gamma)/(1 + beta*gamma) ;
	kQ:= FreeKAlgebra( PolyRing, 4, "x" );
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



ParameterizedAlgebraSInfinity:= function( K )	#(6.1.3), where alpha, beta and gamma are nonzero and not +-1. p.140
  local PolyRing, kQ, alpha, beta, gamma, rels, x1, x2, x3, x4, I, gb, A ;
  PolyRing:= FunctionField( K, [ "beta", "gamma" ] ) ;
  beta:= IndeterminatesOfFunctionField( PolyRing )[1] ;
  gamma:= IndeterminatesOfFunctionField( PolyRing )[2] ;
  alpha:= -(beta + gamma)/(1 + beta*gamma) ;
  kQ:= FreeKAlgebra( PolyRing, 4, "x" );
	x1:= kQ.x1; x2:= kQ.x2; x3:= kQ.x3; x4:= kQ.x4;
	rels:= [ ];
	rels[1]:= Commutator( kQ.x1, kQ.x2 ) - alpha*SkewCommutator( kQ.x3, kQ.x4 ) ;
	rels[2]:= SkewCommutator( kQ.x1, kQ.x2 ) - Commutator( kQ.x3, kQ.x4 ) ;
  #
	rels[3]:= Commutator( kQ.x1, kQ.x3 ) - beta*SkewCommutator( kQ.x4, kQ.x2 );
	rels[4]:= SkewCommutator( kQ.x1, kQ.x3 ) - Commutator( kQ.x4, kQ.x2 );
	rels[5]:= -x1^2 + x2^2 + x3^2 + x4^2 ;
	rels[6]:= x2^2 + ((1+alpha)/(1-beta))*x3^2 + ((1-alpha)/(1+gamma))*x4^2 ;
	#	I:= Ideal( kQ, rels );
	#	gb:= GroebnerBasis( I, rels );
	#A:= kQ/rels ;
	#	A:= GBQuotient( kQ, rels );
	return [ 0, kQ, rels ];
end;



ParameterizedAlgebraSdi:= function( K, i )	#(6.1.4), where alpha, beta and gamma are nonzero and not +-1. p.140
	local PolyRing, kQ, alpha, beta, gamma, d1, d2, rels, x1, x2, x3, x4, j, I, gb, A ;
  PolyRing:= FunctionField( K, [ "d1", "d2", "beta", "gamma" ] ) ;
  d1:= IndeterminatesOfFunctionField( PolyRing )[1] ;
  d2:= IndeterminatesOfFunctionField( PolyRing )[2] ;
  beta:= IndeterminatesOfFunctionField( PolyRing )[3] ;
  gamma:= IndeterminatesOfFunctionField( PolyRing )[4] ;
  alpha:= -(beta + gamma)/(1 + beta*gamma) ;
  kQ:= FreeKAlgebra( PolyRing, 4, "x" );
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



ParameterizedAlgebraSInfinityTwist:= function( K )	#(6.1.3), where alpha, beta and gamma are nonzero and not +-1. p.140
  local PolyRing, kQ, alpha, beta, gamma, rels, x1, x2, x3, x4, I, gb, A ;
  PolyRing:= FunctionField( K, [ "beta", "gamma" ] ) ;
  beta:= IndeterminatesOfFunctionField( PolyRing )[1] ;
  gamma:= IndeterminatesOfFunctionField( PolyRing )[2] ;
  alpha:= -(beta + gamma)/(1 + beta*gamma) ;
  kQ:= FreeKAlgebra( PolyRing, 4, "x" );
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



ParameterizedAlgebraSdiTwist:= function( K, i )	#(6.1.4), where alpha, beta and gamma are nonzero and not +-1. p.141
																												#For this algebra to be AS regular of dimension 4, we need to assume,
																												#if i = 1, that (d1,d2) != (1,0), (1,-1-beta*gamma), and if i = 2,
																												#(d1,d2) != (1, beta-1), (1,-1-gamma)
  local PolyRing, kQ, alpha, beta, gamma, d1, d2, rels, x1, x2, x3, x4, j, I, gb, A ;
  PolyRing:= FunctionField( K, [ "d1", "d2", "beta", "gamma" ] ) ;
  d1:= IndeterminatesOfFunctionField( PolyRing )[1] ;
  d2:= IndeterminatesOfFunctionField( PolyRing )[2] ;
  beta:= IndeterminatesOfFunctionField( PolyRing )[3] ;
  gamma:= IndeterminatesOfFunctionField( PolyRing )[4] ;
  alpha:= -(beta + gamma)/(1 + beta*gamma) ;
  kQ:= FreeKAlgebra( PolyRing, 4, "x" );
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



ParameterizedAlgebraVancliff:= function( K )	#(6.3.1), p.154
																				    #lambda \neq alpha*beta
  local PolyRing, kQ, alpha, beta, lambda, rels, x1, x2, x3, x4, j, I, gb, A ;
  PolyRing:= FunctionField( K, [ "alpha", "beta", "lambda" ] ) ;
  alpha:= IndeterminatesOfFunctionField( PolyRing )[1] ;
  beta:= IndeterminatesOfFunctionField( PolyRing )[2] ;
  lambda:= IndeterminatesOfFunctionField( PolyRing )[3] ;
  kQ:= FreeKAlgebra( PolyRing, 4, "x" );
#	p:= E(4);
	x1:= kQ.x1; x2:= kQ.x2; x3:= kQ.x3; x4:= kQ.x4;
	rels:= [ ];
	rels[1]:= x2*x1 - alpha*x1*x2 ;
	rels[2]:= x3*x1 - lambda*x1*x3 ;
#
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



ParameterizedAlgebraVancliffTwist:= function( K )	#(6.3.6), p.155
																													#lambda \neq alpha*beta
  local PolyRing, kQ, alpha, beta, lambda, rels, x1, x2, x3, x4, j, I, gb, A ;
  PolyRing:= FunctionField( K, [ "alpha", "beta", "lambda" ] ) ;
  alpha:= IndeterminatesOfFunctionField( PolyRing )[1] ;
  beta:= IndeterminatesOfFunctionField( PolyRing )[2] ;
  lambda:= IndeterminatesOfFunctionField( PolyRing )[3] ;
  kQ:= FreeKAlgebra( PolyRing, 4, "x" );
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


####################################################################################################################################################

ParameterizedCliffordAlgebra:= function( K )
  local PolyRing, kQ,
  a121, a122, a123, a124,
  a131, a132, a133, a134,
  a141, a142, a143, a144,
  a231, a232, a233, a234,
  a241, a242, a243, a244,
  a341, a342, a343, a344,
  rels, gb, I, A;
#
  PolyRing:= FunctionField( K, [
  "a121", "a122", "a123", "a124",
  "a131", "a132", "a133", "a134",
  "a141", "a142", "a143", "a144",
  "a231", "a232", "a233", "a234",
  "a241", "a242", "a243", "a244",
  "a341", "a342", "a343", "a344" ] );
  a121:= IndeterminatesOfFunctionField( PolyRing )[1]; a122:= IndeterminatesOfFunctionField( PolyRing )[2];
  a123:= IndeterminatesOfFunctionField( PolyRing )[3]; a124:= IndeterminatesOfFunctionField( PolyRing )[4];
#
  a131:= IndeterminatesOfFunctionField( PolyRing )[5]; a132:= IndeterminatesOfFunctionField( PolyRing )[6];
  a133:= IndeterminatesOfFunctionField( PolyRing )[7]; a134:= IndeterminatesOfFunctionField( PolyRing )[8];
#
  a141:= IndeterminatesOfFunctionField( PolyRing )[9]; a142:= IndeterminatesOfFunctionField( PolyRing )[10];
  a143:= IndeterminatesOfFunctionField( PolyRing )[11]; a144:= IndeterminatesOfFunctionField( PolyRing )[12];
#
  a231:= IndeterminatesOfFunctionField( PolyRing )[13]; a232:= IndeterminatesOfFunctionField( PolyRing )[14];
  a233:= IndeterminatesOfFunctionField( PolyRing )[15]; a234:= IndeterminatesOfFunctionField( PolyRing )[16];
#
  a241:= IndeterminatesOfFunctionField( PolyRing )[17]; a242:= IndeterminatesOfFunctionField( PolyRing )[18];
  a243:= IndeterminatesOfFunctionField( PolyRing )[19]; a244:= IndeterminatesOfFunctionField( PolyRing )[20];
#
  a341:= IndeterminatesOfFunctionField( PolyRing )[21]; a342:= IndeterminatesOfFunctionField( PolyRing )[22];
  a343:= IndeterminatesOfFunctionField( PolyRing )[23]; a344:= IndeterminatesOfFunctionField( PolyRing )[24];
#
  kQ:= FreeKAlgebra( PolyRing, 4, "x" );
  rels:= [];
  rels[1]:= kQ.x1*kQ.x2 + kQ.x2*kQ.x1 + a121*kQ.x1^2 + a122*kQ.x2^2 + a123*kQ.x3^2 + a124*kQ.x4^2 ;
  rels[2]:= kQ.x1*kQ.x3 + kQ.x3*kQ.x1 + a131*kQ.x1^2 + a132*kQ.x2^2 + a133*kQ.x3^2 + a134*kQ.x4^2 ;
  rels[3]:= kQ.x1*kQ.x4 + kQ.x4*kQ.x1 + a141*kQ.x1^2 + a142*kQ.x2^2 + a143*kQ.x3^2 + a144*kQ.x4^2 ;
  rels[4]:= kQ.x2*kQ.x3 + kQ.x3*kQ.x2 + a231*kQ.x1^2 + a232*kQ.x2^2 + a233*kQ.x3^2 + a234*kQ.x4^2 ;
  rels[5]:= kQ.x2*kQ.x4 + kQ.x4*kQ.x2 + a241*kQ.x1^2 + a242*kQ.x2^2 + a243*kQ.x3^2 + a244*kQ.x4^2 ;
  rels[6]:= kQ.x3*kQ.x4 + kQ.x4*kQ.x3 + a341*kQ.x1^2 + a342*kQ.x2^2 + a343*kQ.x3^2 + a344*kQ.x4^2 ;
#  I:= Ideal( kQ, rels );
#  gb:= GroebnerBasis( I, rels );
#  A:= kQ/rels ;
#  A:= GBQuotient( kQ, rels );
	return [ 0, kQ, rels ] ;
end;



ParameterizedCliffordAlgebra2:= function( K )
  local PolyRing, kQ,
  a121, a122, a123, a124,
  a341, a342, a343, a344,
  rels, gb, I, A;
#
  PolyRing:= FunctionField( K, [
  "a121", "a122", "a123", "a124",
  "a341", "a342", "a343", "a344" ] );
  a121:= IndeterminatesOfFunctionField( PolyRing )[1]; a122:= IndeterminatesOfFunctionField( PolyRing )[2];
  a123:= IndeterminatesOfFunctionField( PolyRing )[3]; a124:= IndeterminatesOfFunctionField( PolyRing )[4];
#
  a341:= IndeterminatesOfFunctionField( PolyRing )[5]; a342:= IndeterminatesOfFunctionField( PolyRing )[6];
  a343:= IndeterminatesOfFunctionField( PolyRing )[7]; a344:= IndeterminatesOfFunctionField( PolyRing )[8];
#
  kQ:= FreeKAlgebra( PolyRing, 4, "x" );
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
#  A:= GBQuotient( kQ, rels );
	return [ 0, kQ, rels ] ;
end;



ParameterizedTetrahedronAlgebra:= function( K )
  local PolyRing, kQ, q12, q13, q14, q23, q24, q34, rels, I, gb, A ;
  PolyRing:= FunctionField( K, [ "q12", "q13", "q14", "q23", "q24", "q34" ] ) ;
  q12:= IndeterminatesOfFunctionField( PolyRing )[1]; q13:= IndeterminatesOfFunctionField( PolyRing )[2];
  q14:= IndeterminatesOfFunctionField( PolyRing )[3]; q23:= IndeterminatesOfFunctionField( PolyRing )[4];
  q24:= IndeterminatesOfFunctionField( PolyRing )[5]; q34:= IndeterminatesOfFunctionField( PolyRing )[6];
  kQ:= FreeKAlgebra( PolyRing, 4, "x" );
  rels:= [];
  rels[1]:= kQ.x1*kQ.x2 - q12*kQ.x2*kQ.x1 ;
  rels[2]:= kQ.x1*kQ.x3 - q13*kQ.x3*kQ.x1 ;
  rels[3]:= kQ.x1*kQ.x4 - q14*kQ.x4*kQ.x1 ;
  rels[4]:= kQ.x2*kQ.x3 - q23*kQ.x3*kQ.x2 ;
  rels[5]:= kQ.x2*kQ.x4 - q24*kQ.x4*kQ.x2 ;
  rels[6]:= kQ.x3*kQ.x4 - q34*kQ.x4*kQ.x3 ;
 I:= Ideal( kQ, rels );
 gb:= GroebnerBasis( I, rels );
  #  A:= kQ/I ;
  A:= GBQuotient( kQ, rels );
  return [ A, kQ, rels ] ;
end;



DualOfParameterizedCliffordAlgebra2:= function( K )
  local PolyRing, kQ,
  a121, a122, a123, a124,
  a341, a342, a343, a344,
  rels, gb, I, A;
#
  PolyRing:= FunctionField( K, [
  "a121", "a122", "a123", "a124",
  "a341", "a342", "a343", "a344" ] );
  a121:= IndeterminatesOfFunctionField( PolyRing )[1]; a122:= IndeterminatesOfFunctionField( PolyRing )[2];
  a123:= IndeterminatesOfFunctionField( PolyRing )[3]; a124:= IndeterminatesOfFunctionField( PolyRing )[4];
#
  a341:= IndeterminatesOfFunctionField( PolyRing )[5]; a342:= IndeterminatesOfFunctionField( PolyRing )[6];
  a343:= IndeterminatesOfFunctionField( PolyRing )[7]; a344:= IndeterminatesOfFunctionField( PolyRing )[8];
#
  kQ:= FreeKAlgebra( PolyRing, 4, "x" );
  rels:= [];
  rels[1]:= (1)*kQ.x1*kQ.x2 + (-1)*kQ.x2*kQ.x1 ;
  rels[2]:= (a342/-a341)*kQ.x1^2 + ((a121*a342-a122*a341)/a341)*kQ.x2*kQ.x1 + (1)*kQ.x2^2 ;
  rels[3]:= (1)*kQ.x1*kQ.x3 + (-1)*kQ.x3*kQ.x1 ;
  rels[4]:= (1)*kQ.x2*kQ.x3 + (-1)*kQ.x3*kQ.x2 ;
  rels[5]:= (a343/-a341)*kQ.x1^2 + ((a121*a343-a123*a341)/a341)*kQ.x2*kQ.x1 + (1)*kQ.x3^2 ;
  rels[6]:= (-1/a341)*kQ.x1^2 + (-a121/-a341)*kQ.x2*kQ.x1 + (1)*kQ.x4*kQ.x3 ;
  rels[7]:= (1)*kQ.x1*kQ.x4 + (-1)*kQ.x4*kQ.x1 ;
  rels[8]:= (1)*kQ.x2*kQ.x4 + (-1)*kQ.x4*kQ.x2 ;
  rels[9]:= (-1/a341)*kQ.x1^2 + (-a121/-a341)*kQ.x2*kQ.x1 + (1)*kQ.x3*kQ.x4 ;
  rels[10]:= (a344/-a341)*kQ.x1^2 + ((a121*a344-a124*a341)/a341)*kQ.x2*kQ.x1 + (1)*kQ.x4^2 ;
#  I:= Ideal( kQ, rels );
#  gb:= GroebnerBasis( I, rels );
#  A:= kQ/I ;
#  A:= GBQuotient( kQ, rels );
	return [ 0, kQ, rels ] ;
end;



#################################################################################################################################################################################

#The next algebras are taken from the paper "Graded Clifford Algebras and Graded Skew Clifford Algebras and their Role in the Classification of
#Artin-Schelter Regular Algebras", by Veerapen



ParameterizedSkewCliffordAlgebra:= function( K, n )  #For n = 4, this is exactly the Tetrahedron algebra
	local indlist, indmat, i, j, t, PolyRing, kQ, rels, gens, x, y, I, gb, A;
  indlist:= [ ];
  indmat:= [ ];
  for i in [1..(n-1)] do
    indmat[i]:= [ ];
    for j in [1..(n-i)] do
      t:= X( K, StringFormatted( "t{}{}", i, i+j ) );
      Add( indlist, t ) ;
      Add( indmat[i], t );
    od;
  od;
  PolyRing:= FunctionField( K, indlist );
  kQ:= FreeKAlgebra( PolyRing, n, "x" );
  gens:= NonOneGeneratorsOfAlgebra( kQ );
  rels:= [ ];
  for i in [1..Length(indmat)] do
    for j in [1.. Length(indmat[i])] do
      Add( rels, gens[j+i]*gens[i] - indmat[i][j]*gens[i]*gens[j+i] ) ;
    od;
  od;
# I:= Ideal( kQ, rels );
# gb:= GroebnerBasis( I, rels );
  A:= kQ/rels ;
  # A:= GBQuotient( kQ, rels );
  return [ A, kQ, rels ];
end;




#################################################################################################################################################################################

#The next algebras are taken from the paper "Poisson Structures and Lie Algebroids in Complex Geometry", by Brent Pym

ParameterizedAlgebraL112:= function( K )	#p0 and p1 nonzero scalars in K, lambda in K
  local PolyRing, kQ, p0, p1, lambda, rels, x1, x2, x3, x4, j, I, gb, A ;
  PolyRing:= FunctionField( K, [ "p0", "p1", "lambda" ] ) ;
  p0:= IndeterminatesOfFunctionField( PolyRing )[1] ;
  p1:= IndeterminatesOfFunctionField( PolyRing )[2] ;
  lambda:= IndeterminatesOfFunctionField( PolyRing )[3] ;
  kQ:= FreeKAlgebra( PolyRing, 4, "x" );
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
#######################################################################################################################################################################################################################################

ParameterizedPymAlgebra:= function( K )
  local PolyRing, kQ, b1, b2, b3, c1, c2, c3, d1, d2, d3, rels, I, gb, A, x1, x2, x3, x4 ;
  PolyRing:= FunctionField( K, [ "c1", "c2", "c3", "d1", "d2", "d3" ] ) ;
  c1:= IndeterminatesOfFunctionField( PolyRing )[1] ;
  c2:= IndeterminatesOfFunctionField( PolyRing )[2] ;
  c3:= IndeterminatesOfFunctionField( PolyRing )[3] ;
  d1:= IndeterminatesOfFunctionField( PolyRing )[4] ;
  d2:= IndeterminatesOfFunctionField( PolyRing )[5] ;
  d3:= IndeterminatesOfFunctionField( PolyRing )[6] ;
       b1 := -c3 - 2 ;
	   b2 := -c1 - 2 ;
	   b3 := -c2 - 2 ;
	   kQ:= FreeKAlgebra( PolyRing, 4, "x" ) ;
	   x1:= kQ.x1; x2:= kQ.x2; x3:= kQ.x3; x4:= kQ.x4 ;
	   rels:= [ ];
       rels[1]:= x4*x1 - x1*x4 - x1^2 - x1*((-c3 -2)*x2 + c1*x3) - d1*x2*x3 ;
       rels[2]:= x4*x2 - x2*x4 - x2^2 - x2*((-c1 - 2)*x3 + c2*x1) - d2*x3*x1 ;
       rels[3]:= x4*x3 - x3*x4 - x3^2 - x3*((-c2 - 2)*x1 + c3*x2) - d3*x1*x2 ;
       rels[4]:= x2*x3 - x3*x2;
       rels[5]:= x3*x1 - x1*x3;
       rels[6]:= x1*x2 - x2*x1;
#	   I:= Ideal( kQ, rels ) ;
#	   gb:= GroebnerBasis( I, rels);
	   A:= kQ/rels ;
	   return [ A, kQ, rels ];
end;


ParameterizedNoNameAlgebra:= function( K ) 
    local PolyRing, kQ, q, b, c0, c1, c2, rels, I, gb, A, x1, x2, x3, x4 ;
	PolyRing:= FunctionField( K, [ "q", "b", "c0", "c1", "c2" ] ) ;
    q:= IndeterminatesOfFunctionField( PolyRing )[1] ;
    b:= IndeterminatesOfFunctionField( PolyRing )[2] ;
    c0:= IndeterminatesOfFunctionField( PolyRing )[3] ;
    c1:= IndeterminatesOfFunctionField( PolyRing )[4] ;
    c2:= IndeterminatesOfFunctionField( PolyRing )[5] ;
    kQ:= FreeKAlgebra( PolyRing, 4, "x" ) ;
    x1:= kQ.x1; x2:= kQ.x2; x3:= kQ.x3; x4:= kQ.x4 ;
    rels:= [ ] ;
    rels[1]:= x2*x1 + q*x1*x2 + b*x4^2 + c0*x3^2 ;
    rels[2]:= x4*x2 + q*x2*x4 + b*x1^2 + c1*x3^2 ;
    rels[3]:= x1*x4 + q*x4*x1 + b*x2^2 + c2*x3^2 ;
    rels[4]:= x4*x3 + x3*x4 ;
    rels[5]:= x1*x3 + x3*x1 ;
    rels[6]:= x2*x3 + x3*x2 ;
#    I:= Ideal( kQ, rels ) ;
#	 gb:= GroebnerBasis( I, rels) ;
#    A:= kQ/rels ;
#    A:= GBQuotient( kQ, rels );
	return [ 0, kQ, rels ];
end;




##########################################################################################################################################################################################################################################

# Examples of Cassidy-Vancliff Graded Clifford Algebras and of Complete Intersection

ParameterizedCassidyVancliff5point1:= function( K ) #Need alpha^2 = -1 = beta^2 in K with alpha,beta and gamma not equal 0. For instance, K = Z_101 and alpha = beta = 10
	local PolyRing, kQ, alpha, beta, gamma, rels, A, x1, x2, x3, x4, I, gb;
	PolyRing:= FunctionField( GaussianRationals, ["gamma"] );
    gamma:= IndeterminatesOfFunctionField( PolyRing )[1] ;
	kQ:= FreeKAlgebraNoGeneratorNames( PolyRing, 4, "x" );
	alpha:= E(4)*One(PolyRing) ;
	beta:= E(4)*One(PolyRing) ;
	rels:= [];
	rels[1]:= kQ.x4*kQ.x1 - alpha*kQ.x1*kQ.x4 ;
	rels[2]:= kQ.x3*kQ.x2 - beta*kQ.x2*kQ.x3 ;
#
	rels[3]:= kQ.x3*kQ.x3 - kQ.x1*kQ.x1 ;
	rels[4]:= kQ.x4*kQ.x4 - kQ.x2*kQ.x2 ;
	rels[5]:= kQ.x3*kQ.x1 - kQ.x1*kQ.x3 + kQ.x2*kQ.x2 ;
	rels[6]:= kQ.x4*kQ.x2 - kQ.x2*kQ.x4 + gamma^2*kQ.x1^2 ;
	# I:= Ideal( kQ, rels );
	# gb:= GroebnerBasis( I, rels );
	A:= kQ/rels ;
	# A:= GBQuotient( kQ, rels );
	return [ A, kQ, rels ];
end;




ParameterizedCassidyVancliff5point2:= function( K )	
																											
	local PolyRing, kQ, alpha1, alpha2, beta1, beta2, rels, x1, x2, x3, x4, I, gb, A;
	PolyRing:= FunctionField( K, ["alpha1", "alpha2", "beta1", "beta2"] );
	alpha1:= IndeterminatesOfFunctionField( PolyRing )[1] ;
    alpha2:= IndeterminatesOfFunctionField( PolyRing )[2] ;
    beta1:= IndeterminatesOfFunctionField( PolyRing )[3] ;
    beta2:= IndeterminatesOfFunctionField( PolyRing )[4] ;
	kQ:= FreeKAlgebra( PolyRing, 4, "x" );
#	p:= E(4);
	x1:= kQ.x1; x2:= kQ.x2; x3:= kQ.x3; x4:= kQ.x4;
	rels:= [ ];
	rels[1]:= x3*x1 + x1*x3 - beta2*x2^2 ;
	rels[2]:= x4*x1 + x1*x4 - alpha2*x3^2 ;
	rels[3]:= x2*x3 - x3*x2 ;
	rels[4]:= x4*x4 - x2*x2 ;
	rels[5]:= x4*x2 + x2*x4 - x3^2 ;
	rels[6]:= alpha1*x3^2 + beta1*x2^2 - x1^2 ;
	#	I:= Ideal( kQ, rels );
	#	gb:= GroebnerBasis( I, rels );
	A:= kQ/rels ;
	#	A:= GBQuotient( kQ, rels );
	return [ A, kQ, rels ];
end;


ParameterizedCassidyVancliff5point3:= function( K )	
																											
	local PolyRing, kQ, u13, u14, u24, u34, rels, x1, x2, x3, x4, I, gb, A ;
	PolyRing:= FunctionField( K, [ "u13", "u14", "u24", "u34" ] ) ;
	u13:= IndeterminatesOfFunctionField( PolyRing )[1] ;
    u14:= IndeterminatesOfFunctionField( PolyRing )[2] ;
    u24:= IndeterminatesOfFunctionField( PolyRing )[3] ;
    u34:= IndeterminatesOfFunctionField( PolyRing )[4] ;
	kQ:= FreeKAlgebraNoGeneratorNames( PolyRing, 4, "x" ) ;
#	p:= E(4);
	x1:= kQ.x1; x2:= kQ.x2; x3:= kQ.x3; x4:= kQ.x4;
	rels:= [ ];
	rels[1]:= x1*x3 + u13*x3*x1 ;
	rels[2]:= x1*x4 + u14*x4*x1 ;
	rels[3]:= x3*x4 + u34*x4*x3 ;
	rels[4]:= x4*x4 - x2*x2 ;
	rels[5]:= x2*x3 + x3*x2 + x4*x4 ;
	rels[6]:= x2*x4 + u24*x4*x2 + x1*x1 ;
	#	I:= Ideal( kQ, rels );
	#	gb:= GroebnerBasis( I, rels );
	A:= kQ/rels ;
	#	A:= GBQuotient( kQ, rels );
	return [ A, kQ, rels ];
end;