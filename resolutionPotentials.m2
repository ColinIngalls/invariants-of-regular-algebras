restart
kk=ZZ/101
kk=CC
loadPackage "NumericalAlgebraicGeometry"
R = kk[n_(0,0,0)..n_(3,3,5),p_0..p_20]
S =R[x_0..x_3]
F = S^6
--P = matrix {F_5,F_4,F_3,F_2,F_1,F_0}
P = genericSymmetricMatrix(R,p_0,6)
N = transpose map(S^4,6,(i,j)->sum(0..3,k->n_(k,i,j)*x_k))
xv = transpose matrix(S, {{x_0..x_3}})
omega = (transpose xv)*(transpose N)*P*N*xv
use S
sigma = map(S,S,matrix {{x_3,x_0,x_1,x_2,n_(0,0,0)..n_(3,3,5),p_0..p_20}})

--sig

--gin4 = generators((ideal(x_0..x_3))^4)
--mn4 = toList (transpose gin4)_0

(M,C) = coefficients(sigma(omega)-omega);
I = ideal(C);
eval = map(R,S)
I = ideal eval C;

numericalIrreducibleDecomposition I



slice = ideal ( (0..102)/(i->random(1,R)));


dim slice
degree slice
dim(I+slice)
degree(I+slice)
pd = primaryDecomposition(I+slice)
ISS = saturate I+slice
