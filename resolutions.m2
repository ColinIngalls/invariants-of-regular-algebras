restart

loadPackage "AssociativeAlgebras"
kk = QQ
kk=ZZ/101

--option 0

N = matrix{{1,1,1,1},{1,1,1,1},{1,1,1,1},{1,1,1,1}}
C = skewPolynomialRing(QQ,promote(N,QQ),{a,b,c,d})

-- option 1, works fine.

C=fourDimSklyanin(kk,{a,b,c,d})

-- option 2, doesn't work.

S = kk<|a,b,c,d|>
I = ideal(
    a*b+13*b*a,
    a*c+17*c*a,
    a*d+29*d*a,
    b*c+7*c*b,
    b*d+11*d*b,
    c*d+43*d*c)
C = S/I


------ Code starts here

ev = map(kk,C,{0,0,0,0})
unit = map(C,kk)

d0 = vars C
d1 = rightKernel(d0)
d2 = rightKernel(d1)
d3 = rightKernel(d2)

--d0  = lift(d0,S)
--d1 = lift(d1,S)
--d2 = lift(d2,S)
--d3 = lift(d3,S)

--ncMatrixMult(d1,d2)

--ncMatrixMult(d0,d1)

m3 = coefficients(transpose(d3))
q1 = m3_1
ord1 = m3_0
ord1*q1
transpose d3

m00 = coefficients(d0)
q11 = m00_1 
ord1*q11
d0
d0*q11


Q1=ev(q1)*inverse(ev(q11))

transpose d3
d0*unit(Q1)

-- normalize

d0 = d0*unit(Q1)
d1 = unit(inverse(Q1))*d1

ncMatrixMult(d0,d1)


-- Find Q1 again

m3 = coefficients(transpose(d3))
q1 = m3_1
ord1 = m3_0
ord1*q1
transpose d3

m00 = coefficients(d0)
q11 = m00_1 
ord1*q11
d0
d0*q11



Q1=ev(q1)*inverse(ev(q11))
transpose d3
d0*unit(Q1)


-- Find Q2
S = ambient C
use S
dS2 = lift(d2,S)
dS3 = lift(d3,S)
dS0 = lift(d0,S)
dS1 = lift(d1,S)

tag1 = image transpose(dS2*dS3)
tag2 = image (dS0*dS1) 

g1 =generators tag1
g2 = generators tag2

t1 = map(S^1,S^6,g1)
t2 = map(S^1,S^6,g2)


--ct1 = coefficients t1
--ct2 = coefficients t2


--(dS0*dS1) // (transpose(dS2*dS3))


--q1shifted = map(C^4,C^4,t1)
--q11shifted = map(C^4,C^4,t2)


--q1shifted//(q11shifted)


m2 = coefficients(t1)
q2 = m2_1
ord2 = m2_0

ord2*ev(q2)
transpose(dS2*dS3)

m22 = coefficients(t2)
q22 = m22_1


ord2*ev(q22)
dS0*dS1


--transpose(dS2*dS3)*ev(q22)
--dS0*dS1*ev(q2)

transpose(d2*d3)
d0*d1*inverse(ev(q22))*ev(q2)



Q2 = ev(q2)//ev(q22)

--Q2 = inverse(ev(q22))*ev(q2)



-- find Q3

m3 = coefficients(transpose(dS1*dS2*dS3))
q3 = m3_1
ord3 = m3_0

ord3*ev(q3)
transpose(dS1*dS2*dS3)

m33 = coefficients(dS0*dS1*dS2)
q33 = m33_1

ord3*ev(q33)
dS0*dS1*dS2




--transpose(d1*d2*d3)*inverse(ev(q3))
--d0*d1*d2*inverse(ev(q33))





transpose(dS1*dS2*dS3)
dS0*dS1*dS2*(ev(q3)//ev(q33))

Q3 = ev(q3)//ev(q33)


-----------------------------------------------------------------------------
-- normalize resolution


d0 = d0*inverse(ev(Q1))
d1 = Q1*d1

ncMatrixMult(d0,d1)

--change P1 by inverse(Q1)

Q1 = Q1*inverse(Q1)
Q2 = Q2
Q3 = inverse(tranpose(Q1))*Q3



eigenvalues Q3
