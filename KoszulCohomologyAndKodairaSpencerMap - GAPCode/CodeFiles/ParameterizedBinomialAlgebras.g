
ParameterizedAlgebra1Generic := function(K)             # ae= 1; c= 1 or -1. 
    local PolyRing, kQ, rels, x1, x2, x3, x4, I, gb, A, a, b, d, f;
    PolyRing:= FunctionField( K, [ "a", "b", "d", "f" ] ) ;
    a:= IndeterminatesOfFunctionField( PolyRing )[1] ;
    b:= IndeterminatesOfFunctionField( PolyRing )[2] ;
    d:= IndeterminatesOfFunctionField( PolyRing )[3] ;
    f:=  IndeterminatesOfFunctionField( PolyRing )[4] ;
    kQ:= FreeKAlgebra( PolyRing, 4, "x" );
    rels := [];
    rels[1] := kQ.x1*kQ.x2 - a*kQ.x2*kQ.x1;
    rels[2] := kQ.x1*kQ.x3 - b*kQ.x3*kQ.x4;
    rels[3] := kQ.x1*kQ.x4 - kQ.x4*kQ.x1;
    rels[4] := kQ.x2*kQ.x3 - d*kQ.x3*kQ.x2;
    rels[5] := kQ.x2*kQ.x4 - (1/a)*kQ.x4*kQ.x2;
    rels[6] := kQ.x3*kQ.x1 - f*kQ.x4*kQ.x3;
#	I:= Ideal( kQ, rels );
#	gb:= GroebnerBasis( I, rels );
#	A:= kQ/rels ;
	return [ 0, kQ, rels ];
end;


ParameterizedAlgebra2Generic := function(K)               # b= cf; a= b^5/c^4df^4 = cf/d; e= c^2df/b^2= d/f 
    local PolyRing, kQ, rels, x1, x2, x3, x4, I, gb, A, c, d, f;
    PolyRing:= FunctionField( K, [ "c", "d", "f" ] ) ;
    c:= IndeterminatesOfFunctionField( PolyRing )[1] ;
    d:= IndeterminatesOfFunctionField( PolyRing )[2] ;
    f:= IndeterminatesOfFunctionField( PolyRing )[3] ;
    kQ:= FreeKAlgebra( PolyRing, 4, "x" );
    rels := [];
    rels[1] := kQ.x1*kQ.x1 - ((c*f)/d)*kQ.x2*kQ.x3;
    rels[2] := kQ.x1*kQ.x2 - (c*f)*kQ.x4*kQ.x3;
    rels[3] := kQ.x1*kQ.x4 - c*kQ.x3*kQ.x3;
    rels[4] := kQ.x2*kQ.x2 - d*kQ.x4*kQ.x1;
    rels[5] := kQ.x2*kQ.x4 - (d/f)*kQ.x3*kQ.x1;
    rels[6] := kQ.x3*kQ.x2 - f*kQ.x4*kQ.x4;
#	I:= Ideal( kQ, rels );
#	gb:= GroebnerBasis( I, rels );
#	A:= kQ/rels ;
    return [0, kQ, rels];
end;



ParameterizedAlgebra3Generic := function(K)              # b=1 or -1; e= 1/a; c= 1/fe^2= a^2/f 
    local PolyRing, kQ, rels, x1, x2, x3, x4, I, gb, A, a, d, f;
    PolyRing:= FunctionField( K, [ "a", "d", "f" ] ) ;
    a:= IndeterminatesOfFunctionField( PolyRing )[1] ;
    d:= IndeterminatesOfFunctionField( PolyRing )[2] ;
    f:= IndeterminatesOfFunctionField( PolyRing )[3] ;
    kQ:= FreeKAlgebra( PolyRing, 4, "x" );
    rels := [];
    rels[1] := kQ.x1*kQ.x2 - a*kQ.x2*kQ.x1;
    rels[2] := kQ.x1*kQ.x3 - kQ.x3*kQ.x1;
    rels[3] := kQ.x1*kQ.x4 - (a^2/f)*kQ.x4*kQ.x3;
    rels[4] := kQ.x2*kQ.x2 - d*kQ.x4*kQ.x4;
    rels[5] := kQ.x2*kQ.x3 - (1/a)*kQ.x3*kQ.x2;
    rels[6] := kQ.x3*kQ.x4 - f*kQ.x4*kQ.x1;
    #A:= kQ/rels ;
    return [0, kQ, rels];
end;


ParameterizedAlgebra4Generic := function(K)              # c=1 or -1; f= bd/a 
    local PolyRing, kQ, rels, x1, x2, x3, x4, I, gb, A, a, b, d, e;
    PolyRing:= FunctionField( K, [ "a", "b", "d", "e" ] ) ;
    a:= IndeterminatesOfFunctionField( PolyRing )[1] ;
    b:= IndeterminatesOfFunctionField( PolyRing )[2] ;
    d:= IndeterminatesOfFunctionField( PolyRing )[3] ;
    e:= IndeterminatesOfFunctionField( PolyRing )[4] ;
    kQ:= FreeKAlgebra( PolyRing, 4, "x" );
    rels := [];
    rels[1] := kQ.x1*kQ.x2 - a*kQ.x2*kQ.x4;
    rels[2] := kQ.x1*kQ.x3 - b*kQ.x3*kQ.x4;
    rels[3] := kQ.x1*kQ.x4 - kQ.x4*kQ.x1;
    rels[4] := kQ.x2*kQ.x1 - d*kQ.x4*kQ.x2;
    rels[5] := kQ.x2*kQ.x2 - e*kQ.x3*kQ.x3;
    rels[6] := kQ.x3*kQ.x1 - ((b*d)/a)*kQ.x4*kQ.x3;
    #A:= kQ/rels ;
    return [0, kQ, rels];
end;



ParameterizedAlgebra5Generic := function(K)               # c= f/b^2; e= 1/b; a= df^2/b^2 
   local PolyRing, kQ, rels, x1, x2, x3, x4, I, gb, A, b, d, f;
    PolyRing:= FunctionField( K, [ "b", "d", "f" ] ) ;
    b:= IndeterminatesOfFunctionField( PolyRing )[1] ;
    d:= IndeterminatesOfFunctionField( PolyRing )[2] ;
    f:= IndeterminatesOfFunctionField( PolyRing )[3] ;
    kQ:= FreeKAlgebra( PolyRing, 4, "x" );
    rels := [];
    rels[1] := kQ.x1*kQ.x1 - (d*f^2)/(b^2)*kQ.x3*kQ.x4;
    rels[2] := kQ.x1*kQ.x3 - b*kQ.x4*kQ.x1;
    rels[3] := kQ.x1*kQ.x4 - (f/b^2)*kQ.x2*kQ.x3;
    rels[4] := kQ.x2*kQ.x2 - d*kQ.x4*kQ.x3;
    rels[5] := kQ.x2*kQ.x4 - (1/b)*kQ.x3*kQ.x2;
    rels[6] := kQ.x3*kQ.x1 - f*kQ.x4*kQ.x2;
    #A:= kQ/rels ;
    return [0, kQ, rels];
end;


ParameterizedAlgebra6Generic := function(K)                  # e= 1 or -1; f= cd^2; b= de^2= d 
    local PolyRing, kQ, rels, x1, x2, x3, x4, I, gb, A, a, c, d; 
    PolyRing:= FunctionField( K, [ "a", "c", "d" ] ) ;
    a:= IndeterminatesOfFunctionField( PolyRing )[1] ;
    c:= IndeterminatesOfFunctionField( PolyRing )[2] ;
    d:= IndeterminatesOfFunctionField( PolyRing )[3] ;
    kQ:= FreeKAlgebra( PolyRing, 4, "x" );
    rels := [];
    rels[1] := kQ.x1*kQ.x1 - a*kQ.x3*kQ.x3;
    rels[2] := kQ.x1*kQ.x2 - d*kQ.x4*kQ.x1;
    rels[3] := kQ.x1*kQ.x3 - c*kQ.x2*kQ.x2;
    rels[4] := kQ.x2*kQ.x3 - d*kQ.x3*kQ.x4;
    rels[5] := kQ.x2*kQ.x4 - kQ.x4*kQ.x2;
    rels[6] := kQ.x3*kQ.x1 - (c*d^2)*kQ.x4*kQ.x4;
    #A:= kQ/rels ;
    return [0, kQ, rels];
end;


ParameterizedAlgebra7Generic := function(K)                   # b= c= f= 1/e;  a=  b^2ce^3 =1 
    local PolyRing, kQ, rels, x1, x2, x3, x4, I, gb, A, d, e; 
    PolyRing:= FunctionField( K, [ "d", "e" ] ) ;
    d:= IndeterminatesOfFunctionField( PolyRing )[1] ;
    e:= IndeterminatesOfFunctionField( PolyRing )[2] ;
    kQ:= FreeKAlgebra( PolyRing, 4, "x" );
    rels := [];
    rels[1] := kQ.x1*kQ.x1 - kQ.x3*kQ.x3;
    rels[2] := kQ.x1*kQ.x2 - (1/e)*kQ.x2*kQ.x1;
    rels[3] := kQ.x1*kQ.x4 - (1/e)* kQ.x4*kQ.x1;
    rels[4] := kQ.x2*kQ.x2 - d*kQ.x4*kQ.x4;
    rels[5] := kQ.x2*kQ.x3 - e*kQ.x3*kQ.x2;
    rels[6] := kQ.x3*kQ.x4 - (1/e)*kQ.x4*kQ.x3;
    #A:= kQ/rels ;
    return [0, kQ, rels];
end;



ParameterizedAlgebra8Generic := function(K)              # a= e^3/(b^2*d*f^3);  c= e^2/(b*d*f)
    local PolyRing, kQ, rels, x1, x2, x3, x4, I, gb, A, b, d, e, f;
    PolyRing:= FunctionField( K, [ "b", "d", "e", "f" ] ) ;
    b:= IndeterminatesOfFunctionField( PolyRing )[1] ;
    d:= IndeterminatesOfFunctionField( PolyRing )[2] ;
    e:= IndeterminatesOfFunctionField( PolyRing )[3] ;
    f:= IndeterminatesOfFunctionField( PolyRing )[4] ;
    kQ:= FreeKAlgebra( PolyRing, 4, "x" );
    rels := [];
    rels[1] := kQ.x1*kQ.x1 - e^3/(b^2*d*f^3)*kQ.x2*kQ.x3;
    rels[2] := kQ.x1*kQ.x2 - b*kQ.x3*kQ.x3;
    rels[3] := kQ.x1*kQ.x4 - e^2/(b*d*f)*kQ.x4*kQ.x2;
    rels[4] := kQ.x2*kQ.x2 - d*kQ.x3*kQ.x1;
    rels[5] := kQ.x2*kQ.x4 - e*kQ.x4*kQ.x3;
    rels[6] := kQ.x3*kQ.x4 - f*kQ.x4*kQ.x1;
    #A:= kQ/rels ;
    return [0, kQ, rels];
end;



ParameterizedAlgebra9Generic := function(K)                # a= (b*e^3)/(d^2*f^3); c= (b*e^2)/(d*f)
   local PolyRing, kQ, rels, x1, x2, x3, x4, I, gb, A, b, d, e, f;
    PolyRing:= FunctionField( K, [ "b", "d", "e", "f" ] ) ;
    b:= IndeterminatesOfFunctionField( PolyRing )[1] ;
    d:= IndeterminatesOfFunctionField( PolyRing )[2] ;
    e:= IndeterminatesOfFunctionField( PolyRing )[3] ;
    f:= IndeterminatesOfFunctionField( PolyRing )[4] ;
    kQ:= FreeKAlgebra( PolyRing, 4, "x" );
    rels := [];
    rels[1] := kQ.x1*kQ.x1 - (b*e^3)/(d^2*f^3)*kQ.x3*kQ.x2;
    rels[2] := kQ.x1*kQ.x3 - b*kQ.x2*kQ.x2;
    rels[3] := kQ.x1*kQ.x4 - (b*e^2)/(d*f)*kQ.x4*kQ.x2;
    rels[4] := kQ.x2*kQ.x1 - d*kQ.x3*kQ.x3;
    rels[5] := kQ.x2*kQ.x4 - e*kQ.x4*kQ.x3;
    rels[6] := kQ.x3*kQ.x4 - f*kQ.x4*kQ.x1;
    #A:= kQ/rels ;
    return [0, kQ, rels];
end;


ParameterizedAlgebra10Generic := function(K)            # a= e; c= 1/e 
    local PolyRing, kQ, rels, x1, x2, x3, x4, I, gb, A, b, d, e, f;
    PolyRing:= FunctionField( K, [ "b", "d", "e", "f" ] ) ;
    b:= IndeterminatesOfFunctionField( PolyRing )[1] ;
    d:= IndeterminatesOfFunctionField( PolyRing )[2] ;
    e:= IndeterminatesOfFunctionField( PolyRing )[3] ;
    f:= IndeterminatesOfFunctionField( PolyRing )[4] ;
    kQ:= FreeKAlgebra( PolyRing, 4, "x" );
    rels := [];
    rels[1] := kQ.x1*kQ.x2 - e*kQ.x2*kQ.x1;
    rels[2] := kQ.x1*kQ.x3 - b*kQ.x3*kQ.x2;
    rels[3] := kQ.x1*kQ.x4 - (1/e)*kQ.x4*kQ.x1;
    rels[4] := kQ.x2*kQ.x3 - d*kQ.x3*kQ.x4;
    rels[5] := kQ.x2*kQ.x4 - e*kQ.x4*kQ.x2;
    rels[6] := kQ.x3*kQ.x1 - f*kQ.x4*kQ.x3;
    #A:= kQ/rels ;
    return [0, kQ, rels];
end;


    
