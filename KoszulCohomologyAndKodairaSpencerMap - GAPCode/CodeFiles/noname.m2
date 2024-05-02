restart

kk=ZZ/101

loadPackage "AssociativeAlgebras"

S = kk<|x0,x1,x2,x3|>

q=13,b=12,c0=14,c1=1324,c2=234

I = 
ideal(
x2*x1 + q*x1*x2 + b*x0^2 + c0*x3^2,
  x0*x2 + q*x2*x0 + b*x1^2 + c1*x3^2,
  x1*x0 + q*x0*x1 + b*x2^2 + c2*x3^2,
  x0*x3 + x3*x0,
  x1*x3 + x3*x1,
  x2*x3 + x3*x2)
 C= S/I
restart
kk=QQ
S=kk[x,y]
I = ideal(x^6+y^6-y^4)
R=S/I
phi = icMap(R)
degree phi ideal gens R

restart
n=11
k=6
R=QQ[x_(0,0)..x_(n,n)]

I = minors(k,genericMatrix(R,x_(0,0),n,n));
