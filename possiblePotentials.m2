restart

kk=ZZ/32771

loadPackage "AssociativeAlgebras"

S = kk<|x_0,x_1,x_2,x_3|>
-- T = kk[x_0..x_3]

idS = map(S,S,{x_0,x_1,x_2,x_3})

 u = sum(0..3,i->random(kk)*x_i)
v=sum(0..3,i->random(kk)*x_i)

dx_0 = derivation(S,{1,0,0,0},idS)
dx_1 = derivation(S,{0,1,0,0},idS)
dx_2 = derivation(S,{0,0,1,0},idS)
dx_3 = derivation(S,{0,0,0,1},idS)

use S
rank2 = u^2*v^2-v*u^2*v+v^2*u^2-u*v^2*u
rank2 = u*v*u*v+v*u*v*u
w = x_0^4+x_1^4+x_2^4+x_3^4+u^4+v^4 -- 1,4,6,6... -CY
w = x_0^4+x_1^4+x_2^4+x_3^4+u*v*u*v+v*u*v*u -- 1,4,8,25,69 -CY
w = x_0^4+x_1^4+x_2^4+x_3^4+u^2*v^2+v*u^2*v+v^2*u^2+u*v^2*u --1,4,7,9,11,13,15... -CY
w = x_0*x_1*x_2*x_3-x_1*x_2*x_3*x_0 + x_2*x_3*x_0*x_1 - x_3*x_0*x_1*x_2+u^2*v^2-v*u^2*v+v^2*u^2-u*v^2*u --1,4,4,0 CY
w = x_0*x_1*x_2*x_3-x_1*x_2*x_3*x_0 + x_2*x_3*x_0*x_1 - x_3*x_0*x_1*x_2+ u*v*u*v-v*u*v*u --1,4,5,5,4,1,0  CY
w = x_0*x_1*x_2*x_3+x_1*x_2*x_3*x_0 + x_2*x_3*x_0*x_1 + x_3*x_0*x_1*x_2+ u^4+v^4 --1,4,8,25,69 -CY
w = x_0*x_1*x_2*x_3+x_1*x_2*x_3*x_0 + x_2*x_3*x_0*x_1 + x_3*x_0*x_1*x_2+ u*v*u*v+v*u*v*u --1,4,9,45,192  -CY
w = x_0*x_1*x_2*x_3+x_1*x_2*x_3*x_0 + x_2*x_3*x_0*x_1 + x_3*x_0*x_1*x_2+u^2*v^2+v*u^2*v+v^2*u^2+u*v^2*u --1,4,9,45,192 -CY

w = x_0*x_1*x_0*x_1+x_1*x_0*x_1*x_0+x_2*x_3*x_2*x_3+x_3*x_2*x_3*x_2+u*v*u*v+v*u*v*u --1,4,9,16,25,36 -CY
w = x_0*x_1*x_0*x_1-x_1*x_0*x_1*x_0+x_2*x_3*x_2*x_3-x_3*x_2*x_3*x_2+u*v*u*v-v*u*v*u --1,4,3,0  CY


w = x_0^4+x_1^4+x_2^4+x_3^4 --1,4,4,4,4 -CY


cfs = coefficients w;
mono=cfs_0_199_0
lx0 = leftMultiplicationMap(x_0,3,4)
(transpose lx0)*(ncBasis(4,S))

rels = ((0,0)..(3,3))/((i,j)->(dx_i dx_j w))
A = S/(ideal rels)

dd0 := vars A;
dd1 := rightKernel(dd0);
dd2 := rightKernel(dd1);
dd3 := rightKernel(dd2);
dd4 := rightKernel(dd3);
dd5:=rightKernel(dd4);

R=QQ[t]
factorization(1-4*t+4*t)
