restart

loadPackage "AssociativeAlgebras"

-- compute invarants of the resolution as described in 
--thesis "New Examples of four dimensional AS-regular algebras"
-- examples at end

invariantsFromResolution = (C -> (
kk:=coefficientRing(C);	
ev := map(kk,C,{0,0,0,0});
unit := map(C,kk);

-- compute resolution of k, these are the differentials, called Mi in thesis.

dd0 := vars C;
dd1 := rightKernel(dd0);
dd2 := rightKernel(dd1);
dd3 := rightKernel(dd2);

m3 := coefficients(transpose(dd3));
q1 := m3_1;
ord1 := m3_0;

m00 := coefficients(dd0);
q11 := m00_1;
Q1:=ev(q1)*inverse(ev(q11));

-- We now normalize, change basis so the new Q1 = Id

d0 := dd0*unit(Q1);
d1 := unit(inverse(Q1))*dd1;
d2 := dd2;
d3 := dd3;

-- Find Q2
S := ambient C;
use S;
dS2 := lift(d2,S);
dS3 := lift(d3,S);
dS0 := lift(d0,S);
dS1 := lift(d1,S);

m2 := coefficients(transpose(dS2*dS3));
q2 := m2_1;
ord2 := m2_0;

m22 := coefficients(dS0*dS1);
q22 := m22_1;

evS:=map(kk,S,{0,0,0,0});

Q2 := evS(q2)//evS(q22);

-- find Q3

m32 := coefficients(transpose(dS1*dS2*dS3));
q3 := m32_1;
ord3 := m32_0;

ord3*evS(q3);
transpose(dS1*dS2*dS3);

m33 := coefficients(dS0*dS1*dS2);
q33 := m33_1;

ord3*evS(q33);
dS0*dS1*dS2;

transpose(dS1*dS2*dS3);
dS0*dS1*dS2*(evS(q3)//evS(q33));

w = dS0*dS1*dS2*dS3;

Q3 := evS(q3)//evS(q33);

P := Q2;
Q := Q3;
(P,Q,w)))


-- end of function

--invariantsFromResolution(fourDimSklyanin(kk,{a,b,c,d}))

kk = QQ

-- or if you prefer

kk=ZZ/101

--option 0

N = matrix{
    {1,11,7,13},
    {1/11,1,2,5},
    {1/7,1/2,1,3},
    {1/13,1/5,1/3,1}}

N = matrix{
    {1,11,7,13},
    {1/11,1,2,5},
    {1/7,1/2,1,22},
    {1/13,1/5,1/22,1}}

N = matrix{
    {1,-1,-1,-1},
    {-1,1,-1,-1},
    {-1,-1,1,-1},
    {-1,-1,-1,1}}
C = skewPolynomialRing(QQ,promote(N,QQ),{a,b,c,d})
invariantsFromResolution(C)

-- option 1,

C=fourDimSklyanin(kk,{a,b,c,d})
invariantsFromResolution(C)

-- option 2, 

S = kk<|a,b,c,d|>
I = ideal(
    a*b+13*b*a,
    a*c+17*c*a,
    a*d+29*d*a,
    b*c+7*c*b,
    b*d+11*d*b+45*a*c,
    c*d+13*7*d*c)
C = S/I

kk = QQ
S = kk<|x1,x2,x3,x4|>
I = ideal( (1)*x1*x2+(-101)*x2*x1+103*x4*x4, (1)*x1*x3+(-7)*x3*x1, (1)*x1*x4+(-11)*x4*x1, 
  (1)*x2*x3+(-7)*x3*x2, (1)*x2*x4+(-1/11)*x4*x2, (1)*x3*x4+(-1/7)*x4*x3 )
C=S/I

restart

loadPackage "AssociativeAlgebras"

q21=13; q31=101; q41=203; q32=2003; a =37

kk = QQ

S = kk<|x1,x2,x3,x4|>

I = ideal(
(1)*x1*x2+(-q21)*x2*x1+a*x3*x4, (1)*x1*x3+(-q31)*x3*x1, (1)*x1*x4+(-q41)*x4*x1,
  (1)*x2*x3+(-q32)*x3*x2, (1)*x2*x4+(-q31*q32*q41)^(-1)*x4*x2, (1)*x3*x4+(-q31*q32)^(-1)*x4*x3 )
C=S/I


op = invariantsFromResolution(C)

S = kk<|a,b,c,d|>
I = ideal(
    a*b+b*a+11*a^2+13*b^2+17*c^2+25*d^2,
    a*c+c*a+45*a^2+23*b^2+47*c^2+24*d^2,
    a*d+d*a+14*a^2+53*b^2+27*c^2+23*d^2,
    b*c+c*b+10*a^2+43*b^2+37*c^2+22*d^2,
    b*d+d*b+77*a^2+83*b^2+47*c^2+21*d^2,
    c*d+d*c)
C = S/I
