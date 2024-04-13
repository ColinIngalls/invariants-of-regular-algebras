restart 
--kk=QQ
kk = ZZ/101
--R=kk[y_1..y_4,c_1..c_10]
R=kk[y_1..y_4]
scan(1..10,i->(c_i =random(kk)))
Q1 = sub(diagonalMatrix matrix{{0,1,0,0}},R)
Q2 = sub(diagonalMatrix matrix{{0,0,1,0}},R)
Q3 = sub(diagonalMatrix matrix{{0,0,1,0}},R)
Q4p = random(R^4,R^4)
Q4p = Q4p+transpose(Q4p)
Q4 = Q4p + diagonalMatrix matrix{{1-Q4p_0_0,-Q4p_1_1,-Q4p_2_2,-Q4p_3_3}}
factor det (y_1*Q1+y_2*Q2+y_3*Q3+y_4*Q4)

restart
kk=QQ
R=kk[x,y]
Ifp = ideal(x^2,x*y)
IZ = ideal(x,y)
ck = IZ/Ifp
degree ck
prune ck
