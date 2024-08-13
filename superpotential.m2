debug needsPackage "AssociativeAlgebras"

superpotential = method(Options => {Strategy => "F4"})
superpotential FreeAlgebraQuotient := opts -> B -> (
   -- compute the relations of the Koszul dual out to degree d+e-1
   -- d = number of generatos of the algebra
   -- e = relation degree
   A := ambient B;
   kk := coefficientRing A;
   e := first degree first (ideal B)_*;
   koszI := homogDual ideal B;
   d := numgens B;
   koszIgb := NCGB(koszI,d+e-1,Strategy => opts.Strategy);
   koszB := A/koszI;
   
   -- compute a basis of the Koszul dual
   allBasis := flatten apply(d+e, i -> flatten entries ncBasis(i,koszB));
   
   -- find a generator of the 'top' degree of the Koszul dual
   topDeg := max apply(allBasis, m -> first degree m);
   topForm := ncBasis(topDeg,koszB);
   if numcols topForm != 1 then error "Expected AS-regular algebra.";

   deg1Basis := flatten entries ncBasis(1,A);
   -- phi is the projection map from A to koszB
   phi := map(koszB,A,gens koszB);
   
   -- basis of the entire tensor algebra in the 'correct degree'
   bigBasis := ncBasis(topDeg,A);
   
   -- project the basis of the tensor algebra to the koszul dual to get a coefficient from the top form
   -- and take the sum of the basis with these coeffs as the superpotential
   first flatten entries (bigBasis * (transpose sub(last coefficients(phi bigBasis, Monomials=>topForm),kk)))
)

isSuperpotential = method()
isSuperpotential RingElement := f -> (
   X := matrix entries transpose splitElement f;
   if rank X != numcols X then return false;
   Y := matrix entries transpose splitElement cycleElement f;
   if rank Y != numcols Y then return false;
   P := (Y // X);
   return ((Y - X*P) == 0);
)

cycleElement = method()
cycleElement RingElement := f -> (
   varList := toVariableList f;
   monLen := #(last first varList);
   -- this matches mori-smith's convention
   sum apply(varList, p -> p#0*((p#1)#(monLen-1))*product(drop(p#1,-1)))
)

cycleElement (RingElement, RingMap) := (f,sig) -> (
   varList := toVariableList f;
   monLen := #(last first varList);
   -- this matches mori-smith's convention
   sum apply(varList, p -> p#0*(sig((p#1)#(monLen-1))*product(drop(p#1,-1))))
)

cycleElement (RingElement,ZZ) := (f,n) -> (
   curElt := f;
   for i from 1 to n do curElt = cycleElement curElt;
   curElt
)

cycleElement (RingElement,RingMap,ZZ) := (f,sig,n) -> (
   curElt := f;
   for i from 1 to n do curElt = cycleElement(curElt,sig);
   curElt
)

splitElement = method()
splitElement RingElement := f -> (
   A := ring f;
   kk := coefficientRing A;
   d := first degree f;
   basis1 := flatten entries ncBasis(1,A);
   basisrest := flatten entries ncBasis(d-1,A);
   matrix apply(basis1, x -> apply(basisrest, m -> sub(first flatten entries last coefficients(f,Monomials=>matrix {{x*m}}),kk)))
)

nakayamaAut = method(Options => options superpotential)
nakayamaAut FreeAlgebraQuotient := opts -> B -> (
   sp := superpotential(B,opts);
   X := matrix entries transpose splitElement sp;
   Y := matrix entries transpose splitElement cycleElement sp;
   -- should multiply by (-1)^(gldim + 1) here, but this is expensive to compute and should be known by the user.
   P := (Y // X);
   map(B,B,flatten entries (P*(transpose ncBasis(1,B))))
)

nakayamaAut RingElement := opts -> sp -> (
   A := ring sp;
   X := matrix entries transpose splitElement sp;
   Y := matrix entries transpose splitElement cycleElement sp;
   P := (Y // X);
   map(A,A,flatten entries (P*(transpose ncBasis(1,A))))
)

leftDiff = method()
leftDiff (RingElement, RingElement) := (w,v) -> (
   -- this function selects those monomials from w that start with the
   -- monomial v, delete v from the monomial and keep the coefficient.
   if #(terms v) != 1 then error "Expected a monomial in second argument.";
   curElt := w;
   diffList := last first toVariableList v;
   for var in diffList do (
       curElt = sum for p in toVariableList curElt list (
                   if first p#1 == var then (p#0) * (product drop(p#1,1)) else 0
                );
       if curElt == 0 then return 0;
   );
   curElt
)

derivationQuotientIdeal = method()
derivationQuotientIdeal (RingElement, ZZ) := (w,n) -> (
   -- this method defines the derivation-quotient ideal
   -- of dubois-violette corresponding to w.  It is not verified
   -- that w is a superpotential.  n derivatives are taken on the left.
   if not isHomogeneous w then error "Expected a homogeneous input.";
   A := ring w;
   baseA := coefficientRing A;
   d := first degree w;
   nBasis := flatten entries ncBasis(n,A);
   diffs := apply(nBasis, m -> leftDiff(w,m));
   basisA := ncBasis(d-n,A);
   coeffs := sub(last coefficients(matrix{diffs}, Monomials => basisA),baseA);
   --idealGens := flatten entries (basisA*(mingens image coeffs));
   --ideal idealGens
   ideal NCGB(ideal select(flatten entries (basisA * coeffs), f -> f != 0),d-n)
)

derivationQuotientRing = method(Options => {DegreeLimit => 4})
derivationQuotientRing (RingElement, ZZ) := opts -> (w,n) -> (
   A := ring w;
   I := derivationQuotientIdeal(w,n);
   Igb := NCGB(I,opts#DegreeLimit);
   A / I
)


end

-- works
restart
load "superpotential.m2"
kk = frac(QQ[a,b,c])
M = matrix {{1,a,b},{1/a,1,c},{1/b,1/c,1}}
B = skewPolynomialRing(kk,M,{x,y,z})
nakayamaAut B

-- works
restart
load "superpotential.m2"
A = QQ<|x,y,z|>
I = ideal {x*y - 5*y*x, x*z - 3*z*x, y*z - 2*z*y }
B = A/I
sp = superpotential B
nakayamaAut B

-- works
restart
load "superpotential.m2"
A = QQ<|x,y,z|>
I = ideal {y*x - x*y - x^2, z*x - x*z, z*y - y*z - 2*x*z}
B = A/I
nakayamaAut B

-- works
restart
load "superpotential.m2"
A = QQ<|x,y|>
I = ideal {y*x - x*y - x^2}
B = A/I
sp = superpotential B
nakayamaAut B

-- works
restart
load "superpotential.m2"
kk = frac(QQ[a,b,c])
B = threeDimSklyanin(kk,{a,b,c},{x,y,z}, DegreeLimit => 3, Strategy => "Naive")
sp = superpotential(B,3,Strategy=>"Naive")
nakayamaAut B

-- works
restart
load "superpotential.m2"
kk = QQ
B = fourDimSklyanin(kk,{w,x,y,z}, DegreeLimit => 3)
elapsedTime superpotential(B,4,Strategy=>"Naive")
nakayamaAut B

-- works
restart
load "superpotential.m2"
kk = QQ
A = kk<|t_1,t_2,t_3|>
I = ideal { (t_2 + t_1)*t_1 - t_1*t_2, (t_3+t_2+t_1)*t_1 - t_1*t_3, (t_3 + t_2 + t_1)*t_2 - (t_1 + t_2)*t_3 }
B = A/I
nakayamaAut B

-- works
restart
load "superpotential.m2"
kk = frac(QQ[p])
A = kk<|t_1,t_2,t_3|>
I = ideal { (t_2+t_1)*t_1 - t_1*t_2, t_3*t_1 - p*t_1*t_3, t_3*t_2 - p*t_2*t_3 }
B = A/I
nakayamaAut B

restart
load "superpotential.m2"
kk = QQ
A = kk<|x_4,x_1,x_2,x_3|>
eps = 1_A
I1 = ideal {x_3^2 - x_1*x_2,
            x_4^2 - eps*x_2*x_1,    
	    x_1*x_3 - x_2*x_4,
	    x_3*x_1 - x_2*x_3,
	    x_1*x_4 - eps*x_4*x_2,
	    x_4*x_1 - x_3*x_2}
S = A/I1  
s = superpotential S
isSuperpotential s
nakayamaAut S

restart
load "superpotential.m2"
kk = QQ
A = kk<|x,y|>
I = ideal (x^2*y - y*x^2, x*y^2 - y^2*x)
B = A/I
s = superpotential B
isSuperpotential s
nakayamaAut B

-- commutative polynomial ring
restart
load "superpotential.m2"
kk = ZZ/32009
A = kk<|x,y,z,w|>
sgn = p -> det ((id_(ZZ^(#p)))_p)
omega = sum apply(permutations 4, p -> (sgn p) * (product ({x,y,z,w}_p)));
I = derivationQuotientIdeal(omega,2)
R = derivationQuotientRing(omega,2)
peek (ideal R).cache
R = derivationQuotientRing(omega,2,DegreeLimit => 10)
peek (ideal R).cache
