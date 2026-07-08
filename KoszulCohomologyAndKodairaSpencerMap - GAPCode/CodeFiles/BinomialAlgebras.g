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
