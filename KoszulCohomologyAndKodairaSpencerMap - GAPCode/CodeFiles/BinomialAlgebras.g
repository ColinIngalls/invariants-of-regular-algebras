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

Algebra1Generic := function(K, a, b, d, f)             # ae= 1; c= 1 or -1. Here, c is assumed to be 1.
    local kQ, rels, x1, x2, x3, x4, I, gb, A ;
    kQ := FreeKAlgebra(K, 4, "x");
    rels := [];
    rels[1] := kQ.x1*kQ.x2 - a*kQ.x2*kQ.x1;
    rels[2] := kQ.x1*kQ.x3 - b*kQ.x3*kQ.x4;
    rels[3] := kQ.x1*kQ.x4 - kQ.x4*kQ.x1;
    rels[4] := kQ.x2*kQ.x3 - d*kQ.x3*kQ.x2;
    rels[5] := kQ.x2*kQ.x4 - (1/a)*kQ.x4*kQ.x2;
    rels[6] := kQ.x3*kQ.x1 - f*kQ.x4*kQ.x3;
    #A:= kQ/rels ;
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


Algebra3Generic := function(K, a, d, f)              # b=1 or -1; e= 1/a; c= 1/fe^2= a^2/f. Here, b is assumed to be 1.
    local kQ, rels, x1, x2, x3, x4, I, gb, A ;
    kQ := FreeKAlgebra(K, 4, "x");
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



