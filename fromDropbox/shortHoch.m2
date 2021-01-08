-- Hochschild cohomology of A finite dimensional and commutative

restart
KK=ZZ/31991
n=4
R=KK[x_1..x_n]

idealList1 = 
{ideal(x_1^2-7*x_2^2,x_1*x_2-3*x_2^2,x_3^2,x_4^2),
ideal(x_1^2,x_1*random(1,R)+x_2*random(1,R),random(2,R),random(2,R)),
ideal(x_1^2,x_2^2,x_3^2,random(2,R)),
ideal((x_1+x_2+x_3+x_4)^2,x_1^2,x_2^2,x_3*x_4),
ideal(x_1^2,x_1*random(1,R)+x_2*random(1,R),random(2,R),random(2,R)),
ideal(x_1^2,x_2^2,x_3^2,random(2,R)),
ideal((x_1+x_2+x_3+x_4)^2,x_1^2,x_2^2,x_3*x_4),
ideal(x_1^2+(random(0,R))*x_3*x_4+x_4^2,x_2^2+random(0,R)*x_3*x_4+x_4^2,x_1*x_2*random(0,R)*x_3*x_4+x_4^2,x_3^2+random(0,R)*x_3*x_4+x_4^2)}

a1=random(0,R)
a2=random(0,R)
a3=random(0,R)
a4=random(0,R)
idealList2 = {
ideal(x_1^2+x_2^2+x_3^2+2*x_1*x_2+2*x_1*x_3+2*x_2*x_3+a4*x_4^2,
    x_1^2+a1*x_4^2,x_2^2+a2*x_4^2,x_3^2+a3*x_4^2),
ideal(2*x_1*x_2+2*x_1*x_3+2*x_2*x_3+a4*x_4^2,
    x_1^2+a1*x_4^2,
    x_2^2+a2*x_4^2,
    x_3^2+a3*x_4^2),
ideal(2*x_1*x_2-2*x_1*x_3+a4*x_4^2,
    x_1^2+a1*x_4^2,
    x_2^2+a2*x_4^2,
    x_3^2+a3*x_4^2),
ideal(2*x_2*x_3+a4*x_4^2,
    x_1^2+a1*x_4^2,
    x_2^2+a2*x_4^2,
    2*x_1*x_2-x_3^2+a3*x_4^2),
ideal(2*x_1*x_2+a4*x_4^2,
    x_1^2+a1*x_4^2,
    x_2^2+a2*x_4^2,
    x_3^2+a3*x_4^2)}

idealList3 = {
ideal(x_1^2,x_1*random(1,R)+x_2*random(1,R),random(2,R),random(2,R)),
ideal(x_1^2,x_2^2,x_3^2,random(2,R)),
ideal((x_1+x_2+x_3+x_4)^2,x_1^2,x_2^2,x_3*x_4),
ideal(random(2,R),random(2,R), random(2,R),random(2,R)),
ideal(x_1^2+(random(0,R))*x_3*x_4+x_4^2,x_2^2+random(0,R)*x_3*x_4+x_4^2,x_1*x_2+random(0,R)*x_3*x_4+x_4^2,x_3^2+random(0,R)*x_3*x_4+x_4^2)}

hoch = I->(
RI=R/I;
use RI;
S=tensor(RI,RI,Variables =>{x_1..x_4,y_1..y_4},Degrees=>{1,1,1,1,1,1,1,1});
Idelta=ideal(x_1-y_1,x_2-y_2,x_3-y_3,x_4-y_4);
delta=S^1/Idelta;
apply({1,2},i->(numerator reduceHilbert hilbertSeries(Ext^i(delta,delta)))))

apply(idealList1,hoch)
apply(idealList2,hoch)
apply(idealList3,hoch)
