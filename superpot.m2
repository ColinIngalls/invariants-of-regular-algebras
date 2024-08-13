restart

loadPackage "AssociativeAlgebras"

kk = ZZ/101
R=kk[a_(0,0,0)..a_(3,3,5),b_(0,0,0)..b_(3,3,5)]
S=R<|x_0,x_1,x_2,x_3|>
gg = matrix {generators S}
P_0= genericMatrix(R,a_(0,0,0),4,6)
P_1= genericMatrix(R,a_(1,0,0),4,6)
P_2= genericMatrix(R,a_(2,0,0),4,6)
P_3= genericMatrix(R,a_(3,0,0),4,6)


B = genericMatrix(R,b_(0,0),6,6)
entr = ((0,0)..(3,5))/(v->sum(0..3,j->(a_(j,v_0,v_1)*x_j)))

Pt = map(S^6,S^6,{{0, 0, 0, 0, 0, 1}, {0, 0, 0, 0, 1, 0}, {0, 0, 0, 1, 0,
      0}, {0, 0, 1, 0, 0, 0}, {0, 1, 0, 0, 0, 0}, {1, 0, 0, 0, 0, 0}})


PP=map(S^4,S^6,(i,j)->sum(0..3,k->(a_(k,i,j)*x_k)))

PPb=map(S^4,S^6,(i,j)->sum(0..3,k->(b_(k,i,j)*x_k)))
pot = gg*PP*(transpose PPb)*(transpose gg)

sigma = map(S,S,{x_3,x_0,x_1,x_2})

sigma(pot)

cfs  = sub((coefficients(pot-sigma(pot)))_1,R);

I = ideal cfs


slice = ideal ( (0..150)/(i->random(1,R)));


dim slice
degree slice
dim(I+slice)

dim I
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
    b*d+11*d*b,
    c*d+43*d*c)
C = S/I

invariantsFromResolution(C)

