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
