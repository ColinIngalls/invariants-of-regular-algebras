Algebra1 := function(K)
    local kQ, rels, I;
    kQ := FreeKAlgebra(K, 4, "x");
    rels := [];
    rels[1] := kQ.x1*kQ.x2 - kQ.x2*kQ.x1;
    rels[2] := kQ.x1*kQ.x3 - kQ.x3*kQ.x4;
    rels[3] := kQ.x1*kQ.x4 - kQ.x4*kQ.x1;
    rels[4] := kQ.x2*kQ.x3 - kQ.x3*kQ.x2;
    rels[5] := kQ.x2*kQ.x4 - kQ.x4*kQ.x2;
    rels[6] := kQ.x3*kQ.x1 - kQ.x4*kQ.x3;
    I := Ideal(kQ, rels);
    return [0, kQ, rels];
end;

Algebra2 := function(K)
    local kQ, rels, I;
    kQ := FreeKAlgebra(K, 4, "x");
    rels := [];
    rels[1] := kQ.x1*kQ.x1 - kQ.x2*kQ.x3;
    rels[2] := kQ.x1*kQ.x2 - kQ.x4*kQ.x3;
    rels[3] := kQ.x1*kQ.x4 - kQ.x3*kQ.x3;
    rels[4] := kQ.x2*kQ.x2 - kQ.x4*kQ.x1;
    rels[5] := kQ.x2*kQ.x4 - kQ.x3*kQ.x1;
    rels[6] := kQ.x3*kQ.x2 - kQ.x4*kQ.x4;
    I := Ideal(kQ, rels);
    return [0, kQ, rels];
end;

Algebra3 := function(K)
    local kQ, rels, I;
    kQ := FreeKAlgebra(K, 4, "x");
    rels := [];
    rels[1] := kQ.x1*kQ.x2 - kQ.x2*kQ.x1;
    rels[2] := kQ.x1*kQ.x3 - kQ.x3*kQ.x1;
    rels[3] := kQ.x1*kQ.x4 - kQ.x4*kQ.x3;
    rels[4] := kQ.x2*kQ.x2 - kQ.x4*kQ.x4;
    rels[5] := kQ.x2*kQ.x3 - kQ.x3*kQ.x2;
    rels[6] := kQ.x3*kQ.x4 - kQ.x4*kQ.x1;
    I := Ideal(kQ, rels);
    return [0, kQ, rels];
end;

Algebra4 := function(K)
    local kQ, rels, I;
    kQ := FreeKAlgebra(K, 4, "x");
    rels := [];
    rels[1] := kQ.x1*kQ.x2 - kQ.x2*kQ.x4;
    rels[2] := kQ.x1*kQ.x3 - kQ.x3*kQ.x4;
    rels[3] := kQ.x1*kQ.x4 - kQ.x4*kQ.x1;
    rels[4] := kQ.x2*kQ.x1 - kQ.x4*kQ.x2;
    rels[5] := kQ.x2*kQ.x2 - kQ.x3*kQ.x3;
    rels[6] := kQ.x3*kQ.x1 - kQ.x4*kQ.x3;
    I := Ideal(kQ, rels);
    return [0, kQ, rels];
end;

Algebra5 := function(K)
    local kQ, rels, I;
    kQ := FreeKAlgebra(K, 4, "x");
    rels := [];
    rels[1] := kQ.x1*kQ.x1 - kQ.x3*kQ.x4;
    rels[2] := kQ.x1*kQ.x3 - kQ.x4*kQ.x1;
    rels[3] := kQ.x1*kQ.x4 - kQ.x2*kQ.x3;
    rels[4] := kQ.x2*kQ.x2 - kQ.x4*kQ.x3;
    rels[5] := kQ.x2*kQ.x4 - kQ.x3*kQ.x2;
    rels[6] := kQ.x3*kQ.x1 - kQ.x4*kQ.x2;
    I := Ideal(kQ, rels);
    return [0, kQ, rels];
end;

#Note: 
#In Algebra5 above, if we apply the permutation x1 mapsto x3, x2 mapsto x4, x3 mapsto x1, x4 mapsto x2; we get Algebra KirkmanS. 



Algebra6 := function(K)
    local kQ, rels, I;
    kQ := FreeKAlgebra(K, 4, "x");
    rels := [];
    rels[1] := kQ.x1*kQ.x1 - kQ.x3*kQ.x3;
    rels[2] := kQ.x1*kQ.x2 - kQ.x4*kQ.x1;
    rels[3] := kQ.x1*kQ.x3 - kQ.x2*kQ.x2;
    rels[4] := kQ.x2*kQ.x3 - kQ.x3*kQ.x4;
    rels[5] := kQ.x2*kQ.x4 - kQ.x4*kQ.x2;
    rels[6] := kQ.x3*kQ.x1 - kQ.x4*kQ.x4;
    I := Ideal(kQ, rels);
    return [0, kQ, rels];
end;

Algebra7 := function(K)
    local kQ, rels, I;
    kQ := FreeKAlgebra(K, 4, "x");
    rels := [];
    rels[1] := kQ.x1*kQ.x1 - kQ.x3*kQ.x3;
    rels[2] := kQ.x1*kQ.x2 - kQ.x2*kQ.x1;
    rels[3] := kQ.x1*kQ.x4 - kQ.x4*kQ.x1;
    rels[4] := kQ.x2*kQ.x2 - kQ.x4*kQ.x4;
    rels[5] := kQ.x2*kQ.x3 - kQ.x3*kQ.x2;
    rels[6] := kQ.x3*kQ.x4 - kQ.x4*kQ.x3;
    I := Ideal(kQ, rels);
    return [0, kQ, rels];
end;

Algebra8 := function(K)
    local kQ, rels, I;
    kQ := FreeKAlgebra(K, 4, "x");
    rels := [];
    rels[1] := kQ.x1*kQ.x1 - kQ.x2*kQ.x3;
    rels[2] := kQ.x1*kQ.x2 - kQ.x3*kQ.x3;
    rels[3] := kQ.x1*kQ.x4 - kQ.x4*kQ.x2;
    rels[4] := kQ.x2*kQ.x2 - kQ.x3*kQ.x1;
    rels[5] := kQ.x2*kQ.x4 - kQ.x4*kQ.x3;
    rels[6] := kQ.x3*kQ.x4 - kQ.x4*kQ.x1;
    I := Ideal(kQ, rels);
    return [0, kQ, rels];
end;

Algebra9 := function(K)
    local kQ, rels, I;
    kQ := FreeKAlgebra(K, 4, "x");
    rels := [];
    rels[1] := kQ.x1*kQ.x1 - kQ.x3*kQ.x2;
    rels[2] := kQ.x1*kQ.x3 - kQ.x2*kQ.x2;
    rels[3] := kQ.x1*kQ.x4 - kQ.x4*kQ.x2;
    rels[4] := kQ.x2*kQ.x1 - kQ.x3*kQ.x3;
    rels[5] := kQ.x2*kQ.x4 - kQ.x4*kQ.x3;
    rels[6] := kQ.x3*kQ.x4 - kQ.x4*kQ.x1;
    I := Ideal(kQ, rels);
    return [0, kQ, rels];
end;

Algebra10 := function(K)
    local kQ, rels, I;
    kQ := FreeKAlgebra(K, 4, "x");
    rels := [];
    rels[1] := kQ.x1*kQ.x2 - kQ.x2*kQ.x1;
    rels[2] := kQ.x1*kQ.x3 - kQ.x3*kQ.x2;
    rels[3] := kQ.x1*kQ.x4 - kQ.x4*kQ.x1;
    rels[4] := kQ.x2*kQ.x3 - kQ.x3*kQ.x4;
    rels[5] := kQ.x2*kQ.x4 - kQ.x4*kQ.x2;
    rels[6] := kQ.x3*kQ.x1 - kQ.x4*kQ.x3;
    I := Ideal(kQ, rels);
    return [0, kQ, rels];
end;

Algebra11 := function(K)
    local kQ, rels, I;
    kQ := FreeKAlgebra(K, 4, "x");
    rels := [];
    rels[1] := kQ.x1*kQ.x2 - kQ.x2*kQ.x1;
    rels[2] := kQ.x1*kQ.x3 - kQ.x3*kQ.x1;
    rels[3] := kQ.x1*kQ.x4 - kQ.x4*kQ.x1;
    rels[4] := kQ.x2*kQ.x2 - kQ.x3*kQ.x4;
    rels[5] := kQ.x2*kQ.x3 - kQ.x4*kQ.x4;
    rels[6] := kQ.x3*kQ.x3 - kQ.x4*kQ.x2;
    I := Ideal(kQ, rels);
    return [0, kQ, rels];
end;

Algebra12 := function(K)
    local kQ, rels, I;
    kQ := FreeKAlgebra(K, 4, "x");
    rels := [];
    rels[1] := kQ.x1*kQ.x1 - kQ.x4*kQ.x4;
    rels[2] := kQ.x1*kQ.x2 - kQ.x2*kQ.x1;
    rels[3] := kQ.x1*kQ.x3 - kQ.x3*kQ.x4;
    rels[4] := kQ.x2*kQ.x2 - kQ.x3*kQ.x3;
    rels[5] := kQ.x2*kQ.x4 - kQ.x4*kQ.x2;
    rels[6] := kQ.x3*kQ.x1 - kQ.x4*kQ.x3;
    I := Ideal(kQ, rels);
    return [0, kQ, rels];
end;

Algebra13 := function(K)
    local kQ, rels, I;
    kQ := FreeKAlgebra(K, 4, "x");
    rels := [];
    rels[1] := kQ.x1*kQ.x2 - kQ.x2*kQ.x1;
    rels[2] := kQ.x1*kQ.x3 - kQ.x4*kQ.x2;
    rels[3] := kQ.x1*kQ.x4 - kQ.x3*kQ.x2;
    rels[4] := kQ.x2*kQ.x3 - kQ.x4*kQ.x1;
    rels[5] := kQ.x2*kQ.x4 - kQ.x3*kQ.x1;
    rels[6] := kQ.x3*kQ.x3 - kQ.x4*kQ.x4;
    I := Ideal(kQ, rels);
    return [0, kQ, rels];
end;

Algebra14 := function(K)
    local kQ, rels, I;
    kQ := FreeKAlgebra(K, 4, "x");
    rels := [];
    rels[1] := kQ.x1*kQ.x2 - kQ.x2*kQ.x1;
    rels[2] := kQ.x1*kQ.x3 - kQ.x3*kQ.x1;
    rels[3] := kQ.x1*kQ.x4 - kQ.x4*kQ.x1;
    rels[4] := kQ.x2*kQ.x2 - kQ.x4*kQ.x4;
    rels[5] := kQ.x2*kQ.x3 - kQ.x3*kQ.x2;
    rels[6] := kQ.x3*kQ.x4 - kQ.x4*kQ.x3;
    I := Ideal(kQ, rels);
    return [0, kQ, rels];
end;

Algebra15 := function(K)
    local kQ, rels, I;
    kQ := FreeKAlgebra(K, 4, "x");
    rels := [];
    rels[1] := kQ.x1*kQ.x1 - kQ.x3*kQ.x3;
    rels[2] := kQ.x1*kQ.x2 - kQ.x4*kQ.x3;
    rels[3] := kQ.x1*kQ.x4 - kQ.x2*kQ.x3;
    rels[4] := kQ.x2*kQ.x1 - kQ.x3*kQ.x4;
    rels[5] := kQ.x2*kQ.x2 - kQ.x4*kQ.x4;
    rels[6] := kQ.x3*kQ.x2 - kQ.x4*kQ.x1;
    I := Ideal(kQ, rels);
    return [0, kQ, rels];
end;

Algebra16 := function(K)
    local kQ, rels, I;
    kQ := FreeKAlgebra(K, 4, "x");
    rels := [];
    rels[1] := kQ.x1*kQ.x2 - kQ.x4*kQ.x3;
    rels[2] := kQ.x1*kQ.x3 - kQ.x3*kQ.x1;
    rels[3] := kQ.x1*kQ.x4 - kQ.x2*kQ.x3;
    rels[4] := kQ.x2*kQ.x1 - kQ.x3*kQ.x4;
    rels[5] := kQ.x2*kQ.x4 - kQ.x4*kQ.x2;
    rels[6] := kQ.x3*kQ.x2 - kQ.x4*kQ.x1;
    I := Ideal(kQ, rels);
    return [0, kQ, rels];
end;

Algebra17 := function(K)
    local kQ, rels, I;
    kQ := FreeKAlgebra(K, 4, "x");
    rels := [];
    rels[1] := kQ.x1*kQ.x1 - kQ.x4*kQ.x4;
    rels[2] := kQ.x1*kQ.x2 - kQ.x3*kQ.x1;
    rels[3] := kQ.x1*kQ.x3 - kQ.x2*kQ.x1;
    rels[4] := kQ.x2*kQ.x2 - kQ.x3*kQ.x3;
    rels[5] := kQ.x2*kQ.x4 - kQ.x4*kQ.x3;
    rels[6] := kQ.x3*kQ.x4 - kQ.x4*kQ.x2;
    I := Ideal(kQ, rels);
    return [0, kQ, rels];
end;

Algebra18 := function(K)
    local kQ, rels, I;
    kQ := FreeKAlgebra(K, 4, "x");
    rels := [];
    rels[1] := kQ.x1*kQ.x1 - kQ.x4*kQ.x3;
    rels[2] := kQ.x1*kQ.x2 - kQ.x2*kQ.x1;
    rels[3] := kQ.x1*kQ.x3 - kQ.x3*kQ.x2;
    rels[4] := kQ.x2*kQ.x2 - kQ.x3*kQ.x4;
    rels[5] := kQ.x2*kQ.x4 - kQ.x4*kQ.x1;
    rels[6] := kQ.x3*kQ.x3 - kQ.x4*kQ.x4;
    I := Ideal(kQ, rels);
    return [0, kQ, rels];
end;

Algebra19 := function(K)
    local kQ, rels, I;
    kQ := FreeKAlgebra(K, 4, "x");
    rels := [];
    rels[1] := kQ.x1*kQ.x2 - kQ.x2*kQ.x1;
    rels[2] := kQ.x1*kQ.x3 - kQ.x3*kQ.x1;
    rels[3] := kQ.x1*kQ.x4 - kQ.x4*kQ.x1;
    rels[4] := kQ.x2*kQ.x3 - kQ.x3*kQ.x2;
    rels[5] := kQ.x2*kQ.x4 - kQ.x4*kQ.x2;
    rels[6] := kQ.x3*kQ.x4 - kQ.x4*kQ.x3;
    I := Ideal(kQ, rels);
    return [0, kQ, rels];
end;

Algebra20 := function(K)
    local kQ, rels, I;
    kQ := FreeKAlgebra(K, 4, "x");
    rels := [];
    rels[1] := kQ.x1*kQ.x2 - kQ.x3*kQ.x1;
    rels[2] := kQ.x1*kQ.x3 - kQ.x2*kQ.x1;
    rels[3] := kQ.x1*kQ.x4 - kQ.x4*kQ.x1;
    rels[4] := kQ.x2*kQ.x3 - kQ.x3*kQ.x2;
    rels[5] := kQ.x2*kQ.x4 - kQ.x4*kQ.x3;
    rels[6] := kQ.x3*kQ.x4 - kQ.x4*kQ.x2;
    I := Ideal(kQ, rels);
    return [0, kQ, rels];
end;

Algebra21 := function(K)
    local kQ, rels, I;
    kQ := FreeKAlgebra(K, 4, "x");
    rels := [];
    rels[1] := kQ.x1*kQ.x1 - kQ.x2*kQ.x4;
    rels[2] := kQ.x1*kQ.x2 - kQ.x4*kQ.x4;
    rels[3] := kQ.x1*kQ.x3 - kQ.x3*kQ.x2;
    rels[4] := kQ.x2*kQ.x2 - kQ.x4*kQ.x1;
    rels[5] := kQ.x2*kQ.x3 - kQ.x3*kQ.x4;
    rels[6] := kQ.x3*kQ.x1 - kQ.x4*kQ.x3;
    I := Ideal(kQ, rels);
    return [0, kQ, rels];
end;

Algebra22 := function(K)
    local kQ, rels, I;
    kQ := FreeKAlgebra(K, 4, "x");
    rels := [];
    rels[1] := kQ.x1*kQ.x2 - kQ.x2*kQ.x1;
    rels[2] := kQ.x1*kQ.x3 - kQ.x4*kQ.x1;
    rels[3] := kQ.x1*kQ.x4 - kQ.x3*kQ.x1;
    rels[4] := kQ.x2*kQ.x3 - kQ.x3*kQ.x2;
    rels[5] := kQ.x2*kQ.x4 - kQ.x4*kQ.x2;
    rels[6] := kQ.x3*kQ.x3 - kQ.x4*kQ.x4;
    I := Ideal(kQ, rels);
    return [0, kQ, rels];
end;

Algebra23 := function(K)
    local kQ, rels, I;
    kQ := FreeKAlgebra(K, 4, "x");
    rels := [];
    rels[1] := kQ.x1*kQ.x1 - kQ.x3*kQ.x4;
    rels[2] := kQ.x1*kQ.x2 - kQ.x2*kQ.x4;
    rels[3] := kQ.x1*kQ.x3 - kQ.x4*kQ.x4;
    rels[4] := kQ.x2*kQ.x1 - kQ.x3*kQ.x2;
    rels[5] := kQ.x2*kQ.x3 - kQ.x4*kQ.x2;
    rels[6] := kQ.x3*kQ.x3 - kQ.x4*kQ.x1;
    I := Ideal(kQ, rels);
    return [0, kQ, rels];
end;

Algebra24 := function(K)
    local kQ, rels, I;
    kQ := FreeKAlgebra(K, 4, "x");
    rels := [];
    rels[1] := kQ.x1*kQ.x1 - kQ.x4*kQ.x4;
    rels[2] := kQ.x1*kQ.x2 - kQ.x3*kQ.x4;
    rels[3] := kQ.x1*kQ.x4 - kQ.x2*kQ.x3;
    rels[4] := kQ.x2*kQ.x1 - kQ.x4*kQ.x3;
    rels[5] := kQ.x2*kQ.x2 - kQ.x3*kQ.x3;
    rels[6] := kQ.x3*kQ.x2 - kQ.x4*kQ.x1;
    I := Ideal(kQ, rels);
    return [0, kQ, rels];
end;

Algebra25 := function(K)
    local kQ, rels, I;
    kQ := FreeKAlgebra(K, 4, "x");
    rels := [];
    rels[1] := kQ.x1*kQ.x1 - kQ.x3*kQ.x2;
    rels[2] := kQ.x1*kQ.x2 - kQ.x4*kQ.x3;
    rels[3] := kQ.x1*kQ.x4 - kQ.x2*kQ.x2;
    rels[4] := kQ.x2*kQ.x3 - kQ.x4*kQ.x4;
    rels[5] := kQ.x2*kQ.x4 - kQ.x3*kQ.x1;
    rels[6] := kQ.x3*kQ.x3 - kQ.x4*kQ.x1;
    I := Ideal(kQ, rels);
    return [0, kQ, rels];
end;

Algebra26 := function(K)
    local kQ, rels, I;
    kQ := FreeKAlgebra(K, 4, "x");
    rels := [];
    rels[1] := kQ.x1*kQ.x2 - kQ.x3*kQ.x1;
    rels[2] := kQ.x1*kQ.x3 - kQ.x2*kQ.x1;
    rels[3] := kQ.x1*kQ.x4 - kQ.x4*kQ.x1;
    rels[4] := kQ.x2*kQ.x2 - kQ.x3*kQ.x3;
    rels[5] := kQ.x2*kQ.x4 - kQ.x4*kQ.x3;
    rels[6] := kQ.x3*kQ.x4 - kQ.x4*kQ.x2;
    I := Ideal(kQ, rels);
    return [0, kQ, rels];
end;

Algebra27 := function(K)
    local kQ, rels, I;
    kQ := FreeKAlgebra(K, 4, "x");
    rels := [];
    rels[1] := kQ.x1*kQ.x2 - kQ.x2*kQ.x1;
    rels[2] := kQ.x1*kQ.x3 - kQ.x3*kQ.x4;
    rels[3] := kQ.x1*kQ.x4 - kQ.x4*kQ.x1;
    rels[4] := kQ.x2*kQ.x3 - kQ.x3*kQ.x1;
    rels[5] := kQ.x2*kQ.x4 - kQ.x4*kQ.x2;
    rels[6] := kQ.x3*kQ.x2 - kQ.x4*kQ.x3;
    I := Ideal(kQ, rels);
    return [0, kQ, rels];
end;



################################################################################################################################################################

Algebra1Generic := function(a, d, f)             # ae= 1 
    local Qadj, kQ, rels, x1, x2, x3, x4, I, gb, A, b, c;
    Qadj:= CF(Rationals, 2);
	b:= E(2);
    c:= E(2); 
	kQ:= FreeKAlgebraNoGeneratorNames( Qadj, 4, "x" );
    rels := [];
    rels[1] := kQ.x1*kQ.x2 - a*kQ.x2*kQ.x1;
    rels[2] := kQ.x1*kQ.x3 - b*kQ.x3*kQ.x4;
    rels[3] := kQ.x1*kQ.x4 - c*kQ.x4*kQ.x1;
    rels[4] := kQ.x2*kQ.x3 - d*kQ.x3*kQ.x2;
    rels[5] := kQ.x2*kQ.x4 - (1/a)*kQ.x4*kQ.x2;
    rels[6] := kQ.x3*kQ.x1 - f*kQ.x4*kQ.x3;
#    A:= GBQuotient( kQ, rels );
    return [0, kQ, rels];
end;


    
Algebra2Generic := function(K, c, d, f)               # b= cf; a= b^5/c^4df^4 = cf/d; e= c^2df/b^2= d/f 
    local kQ, rels, x1, x2, x3, x4, I, gb, A ;
    kQ := FreeKAlgebra(K, 4, "x");
    rels := [];
    rels[1] := kQ.x1*kQ.x1 - ((c*f)/d)*kQ.x2*kQ.x3;
    rels[2] := kQ.x1*kQ.x2 - (c*f)*kQ.x4*kQ.x3;
    rels[3] := kQ.x1*kQ.x4 - c*kQ.x3*kQ.x3;
    rels[4] := kQ.x2*kQ.x2 - d*kQ.x4*kQ.x1;
    rels[5] := kQ.x2*kQ.x4 - (d/f)*kQ.x3*kQ.x1;
    rels[6] := kQ.x3*kQ.x2 - f*kQ.x4*kQ.x4;
    #A:= kQ/rels ;
    return [0, kQ, rels];
end;



Algebra3Generic := function(K, a, d, f)              # ae= 1; c= 1/fe^2= a^2/f.
    local kQ, rels, x1, x2, x3, x4, I, gb, A ;
    kQ := FreeKAlgebra(K, 4, "x");
    rels := [];
    rels[1] := kQ.x1*kQ.x2 - a*kQ.x2*kQ.x1;
    rels[2] := kQ.x1*kQ.x3 + kQ.x3*kQ.x1;
    rels[3] := kQ.x1*kQ.x4 - (a^2/f)*kQ.x4*kQ.x3;
    rels[4] := kQ.x2*kQ.x2 - d*kQ.x4*kQ.x4;
    rels[5] := kQ.x2*kQ.x3 - (1/a)*kQ.x3*kQ.x2;
    rels[6] := kQ.x3*kQ.x4 - f*kQ.x4*kQ.x1;
    #A:= kQ/rels ;
    return [0, kQ, rels];
end;



Algebra4Generic := function(K, a, b, d, e)              # c=1 or -1; f= bd/a. Here, c is assumed to be 1.
    local kQ, rels, x1, x2, x3, x4, I, gb, A ;
    kQ := FreeKAlgebra(K, 4, "x");
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


Algebra5Generic := function(K, b, d, f)               # c= f/b^2; e= 1/b; a= df^2/b^2 
   local kQ, rels, x1, x2, x3, x4, I, gb, A ;
    kQ := FreeKAlgebra(K, 4, "x");
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



Algebra6Generic := function(K, a, c, d)                  # e= 1 or -1; f= cd^2; b= de^2= d. Here, e is assumed to be 1.
    local kQ, rels, x1, x2, x3, x4, I, gb, A ;
    kQ := FreeKAlgebra(K, 4, "x");
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


Algebra7Generic := function(K, d, e)                   # b= c= f= 1/e;  a=  b^2ce^3 =1 
    local kQ, rels, x1, x2, x3, x4, I, gb, A ;                  
    kQ := FreeKAlgebra(K, 4, "x");
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


Algebra8Generic := function(K, b, d, e, f)              # a= e^3/(b^2*d*f^3);  c= e^2/(b*d*f)
    local kQ, rels, x1, x2, x3, x4, I, gb, A ;       
    kQ := FreeKAlgebra(K, 4, "x");
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



Algebra9Generic := function(K, b, d, e, f)                # a= (b*e^3)/(d^2*f^3); c= (b*e^2)/(d*f)
   local kQ, rels, x1, x2, x3, x4, I, gb, A ;  
    kQ := FreeKAlgebra(K, 4, "x");
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


Algebra10Generic := function(K, b, d, e, f)            # a= e; c= 1/e 
    local kQ, rels, x1, x2, x3, x4, I, gb, A ; 
    kQ := FreeKAlgebra(K, 4, "x");
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




Algebra11Generic := function(a, d, e, f)          # b = a*p^2 and c = a*p, where p^3 = 1. 
    local Qadj, kQ, p, rels, A, x1, x2, x3, x4;
    Qadj := CF(Rationals, 3);
    p := E(3);
    kQ := FreeKAlgebraNoGeneratorNames(Qadj, 4, "x");
    rels := [];
    rels[1] := kQ.x1*kQ.x2 - a*kQ.x2*kQ.x1;
    rels[2] := kQ.x1*kQ.x3 - (a*p^2)*kQ.x3*kQ.x1;
    rels[3] := kQ.x1*kQ.x4 - (a*p)*kQ.x4*kQ.x1;
    rels[4] := kQ.x2*kQ.x2 - d*kQ.x3*kQ.x4;
    rels[5] := kQ.x2*kQ.x3 - e*kQ.x4*kQ.x4;
    rels[6] := kQ.x3*kQ.x3 - f*kQ.x4*kQ.x2;
    #A := GBQuotient(kQ, rels);
    return [0, kQ, rels];
end;




Algebra12Generic := function(d)                  #a = 1, b = e, c = 1, f = -1, where e^2 = -1
    local kQ, e, rels, A, x1, x2, x3, x4;
    kQ := FreeKAlgebraNoGeneratorNames(GaussianRationals, 4, "x");
    e := E(4);
    rels := [];
    rels[1] := kQ.x1*kQ.x1 - kQ.x4*kQ.x4;
    rels[2] := kQ.x1*kQ.x2 - e*kQ.x2*kQ.x1;
    rels[3] := kQ.x1*kQ.x3 - kQ.x3*kQ.x4;
    rels[4] := kQ.x2*kQ.x2 - d*kQ.x3*kQ.x3;
    rels[5] := kQ.x2*kQ.x4 - e*kQ.x4*kQ.x2;
    rels[6] := kQ.x3*kQ.x1 + kQ.x4*kQ.x3;
    A := GBQuotient(kQ, rels);
    return [A, kQ, rels];
end;




Algebra13Generic := function(K, b, c, e)        # a = 1 or -1; d = b*e/c; f = b/c
    local kQ, rels, x1, x2, x3, x4, I, gb, A;
    kQ := FreeKAlgebra(K, 4, "x");
    rels := [];
    rels[1] := kQ.x1*kQ.x2 - kQ.x2*kQ.x1;
    rels[2] := kQ.x1*kQ.x3 - b*kQ.x4*kQ.x2;
    rels[3] := kQ.x1*kQ.x4 - c*kQ.x3*kQ.x2;
    rels[4] := kQ.x2*kQ.x3 - ((b*e)/c)*kQ.x4*kQ.x1;
    rels[5] := kQ.x2*kQ.x4 - e*kQ.x3*kQ.x1;
    rels[6] := kQ.x3*kQ.x3 - (b/c)*kQ.x4*kQ.x4;
    #A := kQ/rels;
    return [0, kQ, rels];
end;



Algebra14Generic := function(K, a, b, d)         # c = a; e = f = 1
    local kQ, rels, x1, x2, x3, x4, I, gb, A;
    kQ := FreeKAlgebra(K, 4, "x");
    rels := [];
    rels[1] := kQ.x1*kQ.x2 - a*kQ.x2*kQ.x1;
    rels[2] := kQ.x1*kQ.x3 - b*kQ.x3*kQ.x1;
    rels[3] := kQ.x1*kQ.x4 - a*kQ.x4*kQ.x1;
    rels[4] := kQ.x2*kQ.x2 - d*kQ.x4*kQ.x4;
    rels[5] := kQ.x2*kQ.x3 - kQ.x3*kQ.x2;
    rels[6] := kQ.x3*kQ.x4 - kQ.x4*kQ.x3;
    #A := kQ/rels;
    return [0, kQ, rels];
end;



Algebra15Generic := function(K, c, d, f)        # a = c*d; b = c*d*f; e = d*f
    local kQ, rels, x1, x2, x3, x4, I, gb, A;
    kQ := FreeKAlgebra(K, 4, "x");
    rels := [];
    rels[1] := kQ.x1*kQ.x1 - (c*d)*kQ.x3*kQ.x3;
    rels[2] := kQ.x1*kQ.x2 - (c*d*f)*kQ.x4*kQ.x3;
    rels[3] := kQ.x1*kQ.x4 - c*kQ.x2*kQ.x3;
    rels[4] := kQ.x2*kQ.x1 - d*kQ.x3*kQ.x4;
    rels[5] := kQ.x2*kQ.x2 - (d*f)*kQ.x4*kQ.x4;
    rels[6] := kQ.x3*kQ.x2 - f*kQ.x4*kQ.x1;
    #A := kQ/rels;
    return [0, kQ, rels];
end;


Algebra16Generic := function(K, c, d, f)        # a = c*d*f; b = e = 1
    local kQ, rels, x1, x2, x3, x4, I, gb, A;
    kQ := FreeKAlgebra(K, 4, "x");
    rels := [];
    rels[1] := kQ.x1*kQ.x2 - (c*d*f)*kQ.x4*kQ.x3;
    rels[2] := kQ.x1*kQ.x3 - kQ.x3*kQ.x1;
    rels[3] := kQ.x1*kQ.x4 - c*kQ.x2*kQ.x3;
    rels[4] := kQ.x2*kQ.x1 - d*kQ.x3*kQ.x4;
    rels[5] := kQ.x2*kQ.x4 - kQ.x4*kQ.x2;
    rels[6] := kQ.x3*kQ.x2 - f*kQ.x4*kQ.x1;
    #A := kQ/rels;
    return [0, kQ, rels];
end;



Algebra17Generic := function(K, a, d, f)         # b = 1/f; c = 1/(d*f); e = d*f
    local kQ, rels, x1, x2, x3, x4, I, gb, A;
    kQ := FreeKAlgebra(K, 4, "x");
    rels := [];
    rels[1] := kQ.x1*kQ.x1 - a*kQ.x4*kQ.x4;
    rels[2] := kQ.x1*kQ.x2 - (1/f)*kQ.x3*kQ.x1;
    rels[3] := kQ.x1*kQ.x3 - (1/(d*f))*kQ.x2*kQ.x1;
    rels[4] := kQ.x2*kQ.x2 - d*kQ.x3*kQ.x3;
    rels[5] := kQ.x2*kQ.x4 - (d*f)*kQ.x4*kQ.x3;
    rels[6] := kQ.x3*kQ.x4 - f*kQ.x4*kQ.x2;
    #A := kQ/rels;
    return [0, kQ, rels];
end;




Algebra18Generic := function(K, c, d)          # a = c^2*d; b = f = 1; e = 1/c
    local kQ, rels, x1, x2, x3, x4, I, gb, A;
    kQ := FreeKAlgebra(K, 4, "x");
    rels := [];
    rels[1] := kQ.x1*kQ.x1 - (c^2*d)*kQ.x4*kQ.x3;
    rels[2] := kQ.x1*kQ.x2 - kQ.x2*kQ.x1;
    rels[3] := kQ.x1*kQ.x3 - c*kQ.x3*kQ.x2;
    rels[4] := kQ.x2*kQ.x2 - d*kQ.x3*kQ.x4;
    rels[5] := kQ.x2*kQ.x4 - (1/c)*kQ.x4*kQ.x1;
    rels[6] := kQ.x3*kQ.x3 - kQ.x4*kQ.x4;
    #A := kQ/rels;
    return [0, kQ, rels];
end;



Algebra19Generic := function(K, a, b, c, d, e, f)   #no condition on parameters. It's Algebra K_Q[x1,x2,x3,x4] 
    local kQ, rels, x1, x2, x3, x4, I, gb, A;
    kQ := FreeKAlgebra(K, 4, "x");
    rels := [];
    rels[1] := kQ.x1*kQ.x2 - a*kQ.x2*kQ.x1;
    rels[2] := kQ.x1*kQ.x3 - b*kQ.x3*kQ.x1;
    rels[3] := kQ.x1*kQ.x4 - c*kQ.x4*kQ.x1;
    rels[4] := kQ.x2*kQ.x3 - d*kQ.x3*kQ.x2;
    rels[5] := kQ.x2*kQ.x4 - e*kQ.x4*kQ.x2;
    rels[6] := kQ.x3*kQ.x4 - f*kQ.x4*kQ.x3;
    #A := kQ/rels;
    return [0, kQ, rels];
end;



Algebra20Generic := function(K, b, c, f)         # a = b/f; d = e = 1
    local kQ, rels, x1, x2, x3, x4, I, gb, A;
    kQ := FreeKAlgebra(K, 4, "x");
    rels := [];
    rels[1] := kQ.x1*kQ.x2 - (b/f)*kQ.x3*kQ.x1;
    rels[2] := kQ.x1*kQ.x3 - b*kQ.x2*kQ.x1;
    rels[3] := kQ.x1*kQ.x4 - c*kQ.x4*kQ.x1;
    rels[4] := kQ.x2*kQ.x3 - kQ.x3*kQ.x2;
    rels[5] := kQ.x2*kQ.x4 - kQ.x4*kQ.x3;
    rels[6] := kQ.x3*kQ.x4 - f*kQ.x4*kQ.x2;
    #A := kQ/rels;
    return [0, kQ, rels];
end;




Algebra21Generic := function(K, a, d, f)         # b = a*d; c = a/f; e = a*d/f
    local kQ, rels, x1, x2, x3, x4, I, gb, A;
    kQ := FreeKAlgebra(K, 4, "x");
    rels := [];
    rels[1] := kQ.x1*kQ.x1 - a*kQ.x2*kQ.x4;
    rels[2] := kQ.x1*kQ.x2 - (a*d)*kQ.x4*kQ.x4;
    rels[3] := kQ.x1*kQ.x3 - (a/f)*kQ.x3*kQ.x2;
    rels[4] := kQ.x2*kQ.x2 - d*kQ.x4*kQ.x1;
    rels[5] := kQ.x2*kQ.x3 - ((a*d)/f)*kQ.x3*kQ.x4;
    rels[6] := kQ.x3*kQ.x1 - f*kQ.x4*kQ.x3;
    #A := kQ/rels;
    return [0, kQ, rels];
end;



Algebra22Generic := function(K, a, c, e, f)        # b = c*f; d = e
    local kQ, rels, x1, x2, x3, x4, I, gb, A;
    kQ := FreeKAlgebra(K, 4, "x");
    rels := [];
    rels[1] := kQ.x1*kQ.x2 - a*kQ.x2*kQ.x1;
    rels[2] := kQ.x1*kQ.x3 - (c*f)*kQ.x4*kQ.x1;
    rels[3] := kQ.x1*kQ.x4 - c*kQ.x3*kQ.x1;
    rels[4] := kQ.x2*kQ.x3 - e*kQ.x3*kQ.x2;
    rels[5] := kQ.x2*kQ.x4 - e*kQ.x4*kQ.x2;
    rels[6] := kQ.x3*kQ.x3 - f*kQ.x4*kQ.x4;
    #A := kQ/rels;
    return [0, kQ, rels];
end;




Algebra23Generic := function(K, b, d, f)           # a = b*d; c = b*d*f; e = d*f
    local kQ, rels, x1, x2, x3, x4, I, gb, A;
    kQ := FreeKAlgebra(K, 4, "x");
    rels := [];
    rels[1] := kQ.x1*kQ.x1 - (b*d)*kQ.x3*kQ.x4;
    rels[2] := kQ.x1*kQ.x2 - b*kQ.x2*kQ.x4;
    rels[3] := kQ.x1*kQ.x3 - (b*d*f)*kQ.x4*kQ.x4;
    rels[4] := kQ.x2*kQ.x1 - d*kQ.x3*kQ.x2;
    rels[5] := kQ.x2*kQ.x3 - (d*f)*kQ.x4*kQ.x2;
    rels[6] := kQ.x3*kQ.x3 - f*kQ.x4*kQ.x1;
    #A := kQ/rels;
    return [0, kQ, rels];
end;



Algebra24Generic := function(K, a, d, e, f)         # c = 1/f; b = c*d*f = d
    local kQ, rels, x1, x2, x3, x4, I, gb, A;
    kQ := FreeKAlgebra(K, 4, "x");
    rels := [];
    rels[1] := kQ.x1*kQ.x1 - a*kQ.x4*kQ.x4;
    rels[2] := kQ.x1*kQ.x2 - d*kQ.x3*kQ.x4;
    rels[3] := kQ.x1*kQ.x4 - (1/f)*kQ.x2*kQ.x3;
    rels[4] := kQ.x2*kQ.x1 - d*kQ.x4*kQ.x3;
    rels[5] := kQ.x2*kQ.x2 - e*kQ.x3*kQ.x3;
    rels[6] := kQ.x3*kQ.x2 - f*kQ.x4*kQ.x1;
    #A := kQ/rels;
    return [0, kQ, rels];
end;



Algebra25Generic := function(K, c, d, f)            # a = c*d/f; b = d/f; e = 1/(c*d)
    local kQ, rels, x1, x2, x3, x4, I, gb, A;
    kQ := FreeKAlgebra(K, 4, "x");
    rels := [];
    rels[1] := kQ.x1*kQ.x1 - ((c*d)/f)*kQ.x3*kQ.x2;
    rels[2] := kQ.x1*kQ.x2 - (d/f)*kQ.x4*kQ.x3;
    rels[3] := kQ.x1*kQ.x4 - c*kQ.x2*kQ.x2;
    rels[4] := kQ.x2*kQ.x3 - d*kQ.x4*kQ.x4;
    rels[5] := kQ.x2*kQ.x4 - (1/(c*d))*kQ.x3*kQ.x1;
    rels[6] := kQ.x3*kQ.x3 - f*kQ.x4*kQ.x1;
    #A := kQ/rels;
    return [0, kQ, rels];
end;



Algebra26Generic := function(K, b, d, f)            # a = b*d; c = b*d*f; e = f*d
    local kQ, rels, x1, x2, x3, x4, I, gb, A;
    kQ := FreeKAlgebra(K, 4, "x");
    rels := [];
    rels[1] := kQ.x1*kQ.x2 - (b*d)*kQ.x3*kQ.x1;
    rels[2] := kQ.x1*kQ.x3 - b*kQ.x2*kQ.x1;
    rels[3] := kQ.x1*kQ.x4 - (b*d*f)*kQ.x4*kQ.x1;
    rels[4] := kQ.x2*kQ.x2 - d*kQ.x3*kQ.x3;
    rels[5] := kQ.x2*kQ.x4 - (f*d)*kQ.x4*kQ.x3;
    rels[6] := kQ.x3*kQ.x4 - f*kQ.x4*kQ.x2;
    #A := kQ/rels;
    return [0, kQ, rels];
end;



Algebra27Generic := function(K, b, d, e, f)          # a = e; c = 1/e
    local kQ, rels, x1, x2, x3, x4, I, gb, A;
    kQ := FreeKAlgebra(K, 4, "x");
    rels := [];
    rels[1] := kQ.x1*kQ.x2 - e*kQ.x2*kQ.x1;
    rels[2] := kQ.x1*kQ.x3 - b*kQ.x3*kQ.x4;
    rels[3] := kQ.x1*kQ.x4 - (1/e)*kQ.x4*kQ.x1;
    rels[4] := kQ.x2*kQ.x3 - d*kQ.x3*kQ.x1;
    rels[5] := kQ.x2*kQ.x4 - e*kQ.x4*kQ.x2;
    rels[6] := kQ.x3*kQ.x2 - f*kQ.x4*kQ.x3;
    #A := kQ/rels;
    return [0, kQ, rels];
end;