-- Hochschild cohomology of A finite dimensional and commutative

restart
KK=ZZ/31991
n=4
S=KK[x_1..x_n]
R=KK[x_1..x_n,t,s,r]
phi=map(R,S)
R=S

--I=ideal(x_1*x_2,x_3*x_4*t+x_1^2,(x_1+x_2+x_3+x_4)*random(1,R),x_1^2+)


I=ideal(x_1*x_2,x_3*x_4,(x_1+x_2+x_3+x_4)*phi(random(1,S)),s*phi(random(2,S))+t*phi(random(2,S))+r*phi(random(2,S)))


--I=ideal(x_1^2,x_1*random(1,R)+x_2*random(1,R),random(2,R),random(2,R))
--I=ideal(x_1^2,x_2^2,x_3^2,random(2,R))
--I=ideal(random(2,R)+t*random(2,R),random(2,R),random(2,R),random(2,R))
--I=ideal((x_1+x_2+x_3+x_4)^2,x_1^2,x_2^2,x_3*x_4)

--I=ideal(phi random(2,S)+t*phi random(2,S),phi random(2,S),phi random(2,S),phi random(2,S))




--SR=KK[x_1..x_(n-1)]
--fff=map(R,SR)
--use R
--I=ideal(fff(random(2,SR)),fff(random(2,SR)),fff(random(2,SR)),random(2,R))
--I=ideal(x_1*x_2,x_3*(x_1+x_2+x_3),fff(random(2,SR)),random(2,R))
I = ideal(x_1^2+(random(0,S))*x_3*x_4+x_4^2,x_2^2+random(0,S)*x_3*x_4+x_4^2,x_1*x_2*random(0,S)*x_3*x_4+x_4^2,x_3^2+random(0,S)*x_3*x_4+x_4^2)

RI=R/I
reduceHilbert hilbertSeries(RI/ideal (t,s-1,r-1))


T=KK[x_1..x_4,y_1..y_4,t,s,r]
pi1=map(T,R,{x_1..x_4,t,s,r})
pi2=map(T,R,{y_1..y_4,t,s,r})

IT=pi1(I)+pi2(I)
T2=T/IT
Delta=ideal(x_1-y_1,x_2-y_2,x_3-y_3,x_4-y_4)
E=Ext^2(T2^1/Delta,T2^1/Delta)

A=KK[sa,ta]
p=map(T2,A,{s,t})

hilbertSeries E
dim E
E



ES=saturate( image presentation E,ideal(s,r))
Esat=(target presentation E)/ES

pE=pushForward(p,Esat)

prune pE
rank pE
res pE
ring pE
saturate( image presentation pE,ideal(sa,sr))

AA=KK[s,t]
phi=map(AA,A,{1,s,t}) 
Eovert=prune phi (presentation pE)
Et=image Eovert
Etsat=saturate (Et,t)/Et
minimalPresentation (Etsat)
 
presentation Etsat
betti prune cokernel Eovert





end




restart
KK=ZZ/31991
n=4
--S=KK[x_1..x_n]
R=KK[x_1..x_n]
--phi=map(R,S)



I=ideal(x_1^2-7*x_2^2,x_1*x_2-3*x_2^2,x_3^2,x_4^2)

--I=ideal(x_1*x_2,x_3*x_4*t+x_1^2,(x_1+x_2+x_3+x_4)*random(1,R),x_1^2+)


--I=ideal(x_1*x_2,x_3*x_4,(x_1+x_2+x_3+x_4)*phi(random(1,S)),s*phi(random(2,S))+t*phi(random(2,S)))
a1= random(0,R)
a2= random(0,R)
a3= random(0,R)
a4= random(0,R)

--Cayley cubic:
I = ideal(x_1^2+x_2^2+x_3^2+2*x_1*x_2+2*x_1*x_3+2*x_2*x_3+a4*x_4^2,
    x_1^2+a1*x_4^2,x_2^2+a2*x_4^2,x_3^2+a3*x_4^2)
-- (i) one extra nc def cayley cubic 9 comm 10 nc
I = ideal(2*x_1*x_2+2*x_1*x_3+2*x_2*x_3+a4*x_4^2,
    x_1^2+a1*x_4^2,
    x_2^2+a2*x_4^2,
    x_3^2+a3*x_4^2)

-- Dolgachev (ii) classical alg geo page 506, 9 comm 10 nc
I = ideal(2*x_1*x_2-2*x_1*x_3+a4*x_4^2,
    x_1^2+a1*x_4^2,
    x_2^2+a2*x_4^2,
    x_3^2+a3*x_4^2)

-- (iii) has 10 comm defs and 13 nc defs
I = ideal(2*x_2*x_3+a4*x_4^2,
    x_1^2+a1*x_4^2,
    x_2^2+a2*x_4^2,
    2*x_1*x_2-x_3^2+a3*x_4^2)

-- (vii) has 10 comm defs and 13 nc defs
I = ideal(2*x_1*x_2+a4*x_4^2,
    x_1^2+a1*x_4^2,
    x_2^2+a2*x_4^2,
    x_3^2+a3*x_4^2)

I=ideal(x_1^2,x_1*random(1,R)+x_2*random(1,R),random(2,R),random(2,R))
I=ideal(x_1^2,x_2^2,x_3^2,random(2,R))

--I=ideal(random(2,R)+t*random(2,R),random(2,R),random(2,R),random(2,R))
I=ideal((x_1+x_2+x_3+x_4)^2,x_1^2,x_2^2,x_3*x_4)
factor determinant jacobian I
I=ideal(random(2,R),random(2,R), random(2,R),random(2,R))

I = ideal(x_1^2+(random(0,R))*x_3*x_4+x_4^2,x_2^2+random(0,R)*x_3*x_4+x_4^2,x_1*x_2+random(0,R)*x_3*x_4+x_4^2,x_3^2+random(0,R)*x_3*x_4+x_4^2)



dim I
degree I
RI=R/I
dim RI
degree RI
reduceHilbert hilbertSeries RI
l1=(jacobian I)_0_0
phi=map(RI,R)
use RI
reduceHilbert hilbertSeries (ideal(0_RI):ideal(phi(l1)))
S=tensor(RI,RI,Variables =>{x_1..x_4,y_1..y_4},Degrees=>{1,1,1,1,1,1,1,1})
reduceHilbert hilbertSeries(S)
Idelta=ideal(x_1-y_1,x_2-y_2,x_3-y_3,x_4-y_4)
delta=S^1/Idelta
J=jacobian I
omega=coker ((jacobian I)**RI)
T1=coker ((transpose jacobian I)**RI)
ht1=reduceHilbert hilbertSeries T1
reduceHilbert hilbertSeries omega
reduceHilbert hilbertSeries delta
reduceHilbert hilbertSeries Hom(delta,delta)
hh1=reduceHilbert hilbertSeries(Ext^1(delta,delta))
hh2=reduceHilbert hilbertSeries (Ext^2(delta,delta))
-- hilbert series is Sum dim(M_i) t^i
reduceHilbert hh2-ht1
use RI
(ideal(0_RI):phi(ideal(J_3_3,J_3_2)))

generators Ext^2(delta,delta)

use RI
reduceHilbert hilbertSeries ideal(x_1*x_2)

reduceHilbert hilbertSeries image  (gens ideal (generators RI))

use RI
reduceHilbert hilbertSeries ideal (x_1)

Hom(omega,RI)
reduceHilbert hilbertSeries  Ext^0(omega,RI^1)
reduceHilbert hilbertSeries (kernel (jacobian I)**RI)
reduceHilbert hilbertSeries Hom(exteriorPower(2,omega),RI^1)
FR=resolution omega
dualFR=Hom(FR,RI^1)
hilbertSeries HH^4(dualFR)
FD=resolution(delta,DegreeLimit=>4)
Com=Hom(FD,delta);
Com.dd_(-3)
Com_-1
source Com.dd_(-2)
target Com.dd_(-2)

reduceHilbert hilbertSeries kernel Com.dd_(-2)
reduceHilbert hilbertSeries HH^(2) Com
generators HH^2 Com
reduceHilbert hilbertSeries cokernel((jacobian I)**RI)


restart
KK=ZZ/31991
R=KK[x,y,z,w]
S=KK[X,Y,Z,W]
I=ideal((X*Y-Z^2),random(2,S),random(2,S),random(2,S))
 jacobian I
A=random(R^{1,1,1,1},R^4)
Q=(ideal det (A+transpose A))
degree ideal singularLocus Q
jacobian Q

pd=primaryDecomposition ideal singularLocus ideal det jacobian I
degree pd_0
dim pd_0
degree pd_1
dim pd_1
pd_0
dim singularLocus pd_0
v=matrix ideal gens R

restart
R=QQ[x1,x2,x3,x4]
I=ideal(x1*x2*x3*x4)
J=saturate radical ideal singularLocus I
dim J 
degree J
X=Proj (R/J)
HH^1(OO_X)
HH^0(OO_X)
