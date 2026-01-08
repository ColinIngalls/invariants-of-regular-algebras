
loadPackage "AssociativeAlgebras"

// Algebra A
makeAlgA = (h) -> (
    kk := QQ;
    Falg  := kk<|x,y,z,w|>;   
    I  := ideal(
        w*x - x*w,  
        z*y - y*z - y^2, 
        y*w - h*w*y, 
        y*x - h*(w*z + x*y), 
        z*w - h*w*z, 
        z*x + h*((2)*x*y + w*z - x*z)
    );
    Falg / I
)
 A = makeAlgA(h)



// Algebra B
makeAlgB = (h) -> (
    kk := QQ[p]/(p^2 + 1);   
    Falg  := kk<|x,y,z,w|>;    
    I  := ideal(
        x*w - p*w*x,
        z*y - p*y*z,
        y*w + h*(-x*z),
        y*x + h*(-w*z),
        z*w + h*(x*y),
        z*x + h*(-w*y)
    );
    Falg / I
)
 B = makeAlgB(h)



// Algebra C 
makeAlgC = (h) -> (
    kk := QQ[p]/(p^2 + p + 1);
    Falg  := kk<|x,y,z,w|>;    
    I  := ideal(
        z*y - p*y*z,
        x*w - p*w*x,
        y*w + h*(w*y - (p^2)*x*y - w*z + p*x*z),
        y*x + h*(p*w*y - x*y - w*z + p*x*z),
        z*w + h*(p*w*y + 2*(p^2)*x*y - p*w*z + p*x*z),
        z*x + h*(p*w*y - (p^2)*x*y - w*z + x*z)
    );
    Falg / I
)
 C = makeAlgC(h)


 // Algebra D
makeAlgD = (h,p) -> (
    kk := QQ;
    Falg  := kk<|x,y,z,w|>;    
    I  := ideal(
        w*x + x*w,
        z*y - p*y*z,
        y*w + h*(p*w*y),
        y*x + h*((p*p)*x*y - w*z),
        z*w - h*(p*w*z),
        z*x + h*(-w*y - x*z)
    );
    Falg / I
)
 D = makeAlgD(h,p)



 // Algebra E
makeAlgE = (h) -> (
    kk := QQ[p]/(p^2 + 1);   
    Falg  := kk<|x,y,z,w|>;    
    I  := ideal(
        x*w + w*x, 
        z*y - p*y*z, 
        y*w + h*(-w*z - x*z ), 
        y*x + h*(-w*z + x*z ), 
        z*w + h*(w*y - x*y ),  
        z*x + h*(-w*y - x*y )
    );
    Falg / I
)
 E = makeAlgE(h)



 // Algebra F
makeAlgF = (h) -> (
    kk := QQ[p]/(p^2 + 1);   
    Falg  := kk<|x,y,z,w|>;    
    I  := ideal(
        x*w + w*x, 
        z*y - p*y*z, 
        y*w + h*(w*y + p*x*y - w*z + x*z),  
        y*x + h*(p*w*y - x*y - w*z - x*z ), 
        z*w + h*(p*w*y - p*x*y - p*w*z - x*z),
        z*x + h*(p*w*y + p*x*y - w*z + p*x*z)
    );
    Falg / I
)
 F = makeAlgF(h)



 // Algebra G
makeAlgG = (h,p,f) -> (
    kk := QQ;
    Falg  := kk<|x,y,z,w|>;    
    I  := ideal(
        x*w - w*x, 
        z*y - p*y*z, 
        y*w + h*(-p*w*y), 
        y*x + h*(-p*w*y - (p*p)*x*y - w*z),
        z*w + h*(-p*w*z),
        z*x + h*(-f*w*y + w*z - x*z )
    );
    Falg / I
)
 G = makeAlgG(h,p,f)



 // Algebra H
makeAlgH = (h,f) -> (
    kk := QQ;
    Falg  := kk<|x,y,z,w|>;    
    I  := ideal(
        x*w - w*x - w*w, 
        z*y + y*z, 
        y*w - h*w*z, 
        y*x - h*f*w*z - h*x*z, 
        z*w - h*w*y, 
        z*x - h*f*w*y-h*x*y
    );
    Falg / I
)
 H = makeAlgH(h,f)



 // Algebra I
makeAlgI = (h) -> (
    kk := QQ[p]/(p^2 + 1);   
    Falg  := kk<|x,y,z,w|>;    
    I  := ideal(
        x*w - p*w*x,
        z*y + y*z,
        y*w + h*(p*w*y + p*x*y - w*z + p*x*z ),
        y*x + h*(-w*y - x*y - w*z + p*x*z ),
        z*w + h*( -w*y - p*x*y - p*w*z + p*x*z ),
        z*x + h*(w*y + p*x*y - w*z + x*z )
    );
    Falg / I
)
 Ia = makeAlgI(h)



 // Algebra J
makeAlgJ = (h) -> (
    kk := QQ[p]/(p^2 + 1);   
    Falg  := kk<|x,y,z,w|>;    
    I  := ideal(
        x*w - p*w*x, 
        z*y + y*z,
        y*w + h*(-x*y - x*z ),
        y*x + h*(w*y - w*z ),
        z*w + h*(-x*y + x*z ),
        z*x + h*(-w*y - w*z )   
    );
    Falg / I
)
 J = makeAlgJ(h)



 // Algebra K
makeAlgK = (h,q,f) -> (
    kk := QQ;
    Falg  := kk<|x,y,z,w|>;    
    I  := ideal(
        x*w - q*w*x,
        z*y + y*z,
        y*w + h*(-w*y),
        y*x + h*(-x*z),
        z*w + h*(-w*z),
        z*x + h*(-f*x*y)
    );
    Falg / I
)
 K = makeAlgK(h,q,f)



 // Algebra L
makeAlgL = (h,q,f) -> (
    kk := QQ;
    Falg  := kk<|x,y,z,w|>;    
    I  := ideal(
        x*w - q*w*x,
        z*y + y*z,
        y*w + h*(-f*w*z),
        y*x + h*(-x*z),
        z*w + h*(-f*w*y),
        z*x + h*(-x*y)
    );
    Falg / I
)
 L = makeAlgL(h,q,f)



 // Algebra M 
makeAlgM = (h,f) -> (
    kk := QQ;
    Falg  := kk<|x,y,z,w|>;    
    I  := ideal(
        x*w + w*x,
        z*y + y*z,
        y*w + h*(-x*y - w*z ),
        y*x + h*(-f*w*y + x*z ),
        z*w + h*(-w*y + x*z ),
        z*x + h*(x*y + f*w*z )
    );
    Falg / I
)
 M = makeAlgM(h,f)



 // Algebra N 
makeAlgN = (h,f,g) -> (
    kk := QQ;
    Falg  := kk<|x,y,z,w|>;    
    I  := ideal(
        x*w + w*x,
        z*y + y*z,
        y*w + h*(g*x*y - f*x*z ),
        y*x + h*(-g*w*y - f*w*z ),
        z*w + h*(-f*x*y + g*x*z ),
        z*x + h*(-f*w*y - g*w*z )   
    );
    Falg / I
)
 N = makeAlgN(h,f,g)



 // Algebra O
makeAlgO = (h,f) -> (
    kk := QQ;
    Falg  := kk<|x,y,z,w|>;    
    I  := ideal(
        x*w + w*x,
        z*y + y*z,
        y*w + h*(-w*y - f*x*z ),
        y*x + h*(x*y - w*z ),
        z*w + h*(-f*x*y + w*z ),
        z*x + h*(-w*y - x*z )     
    );
    Falg / I
)
 O = makeAlgO(h,f)



 // Algebra P
makeAlgP = (h,f) -> (
    kk := QQ;
    Falg  := kk<|x,y,z,w|>;    
    I  := ideal(
        x*w + w*x,
        z*y + y*z,
        y*w + h*(-w*z - f*x*z ),
        y*x + h*(-w*z - x*z ),
        z*w + h*(-w*y + f*x*y ),
        z*x + h*(w*y - x*y )   
    );
    Falg / I
)
 P = makeAlgP(h,f)



 // Algebra Q
makeAlgQ = (h) -> (
    kk := QQ;
    Falg  := kk<|x,y,z,w|>;    
    I  := ideal(
        x*w + w*x,
        z*y + y*z,
        y*w + h*(-w*z),
        y*x + h*(-w*y - x*y - w*z ),
        z*w + h*(w*y ),
        z*x + h*(-w*y + w*z - x*z ) 
    );
    Falg / I
)
 Q = makeAlgQ(h)



 // Algebra R
makeAlgR = (h) -> (
    kk := QQ;
    Falg  := kk<|x,y,z,w|>;    
    I  := ideal(
        x*w + w*x, 
        z*y + y*z,
        y*w + h*(-w*y - x*y - w*z ),
        y*x + h*(-w*z ),
        z*w + h*(-x*y ),
        z*x + h*(x*y + w*z - x*z )
    );
    Falg / I
)
 R = makeAlgR(h) 



 // Algebra S
makeAlgS = (h) -> (
    kk := QQ;
    Falg  := kk<|x,y,z,w|>;    
    I  := ideal(
        x*w + w*x,
        z*y + y*z,
        y*w + h*(w*y - x*y - w*z - x*z ),
        y*x + h*(-w*y + x*y - w*z - x*z ),
        z*w + h*(-w*y - x*y + w*z - x*z ),
        z*x + h*(-w*y - x*y - w*z + x*z )
    );
    Falg / I
)
 S = makeAlgS(h) 



 // Algebra T
makeAlgT = (h) -> (
    kk := QQ;
    Falg  := kk<|x,y,z,w|>;    
    I  := ideal(
        x*w + w*x,
        z*y + y*z,
        y*w + h*(w*y - x*y - w*z - x*z),
        y*x + h*(-w*y + x*y - w*z - x*z),
        z*w + h*(-w*y - x*y - w*z + x*z ),
        z*x + h*(-w*y - x*y + w*z - x*z )  
    );
    Falg / I
)
 T = makeAlgT(h) 



 // Algebra U
makeAlgU = (h) -> (
    kk := QQ;
    Falg  := kk<|x,y,z,w|>;    
    I  := ideal(
        x*w + w*x,
        z*y + y*z,
        y*w + h*(w*y - x*y - w*z - x*z ),
        y*x + h*(-w*y - x*y - w*z + x*z ),
        z*w + h*(-w*y - x*y + w*z - x*z ),
        z*x + h*(-w*y + x*y - w*z - x*z )    
    );
    Falg / I
)
 U = makeAlgU(h) 



 // Algebra V
makeAlgV = (h) -> (
    kk := QQ;
    Falg  := kk<|x,y,z,w|>;    
    I  := ideal(
        x*w - w*x,
        z*y + y*z,
        y*w + h*(-x*y - w*z ),
        y*x - h*x*y,
        z*w + h*(w*y - x*y ),
        z*x - h*x*z  
    );
    Falg / I
)
 V = makeAlgV(h) 



 // Algebra W
makeAlgW = (h,f) -> (
    kk := QQ;
    Falg  := kk<|x,y,z,w|>;    
    I  := ideal(
        x*w - w*x,
        z*y + y*z,
        y*w + h*(-f*x*y - w*z ),
        y*x + h*(-w*y + x*z ),
        z*w + h*(-w*y - f*x*z ),
        z*x + h*(x*y - w*z )   
    );
    Falg / I
)
 W = makeAlgW(h,f) 



 // Algebra X
makeAlgX = (h) -> (
    kk := QQ;
    Falg  := kk<|x,y,z,w|>;    
    I  := ideal(
        x*w - w*x,
        z*y + y*z,
        y*w + h*(-w*z),
        y*x + h*(-w*z - x*z ),
        z*w + h*(-w*y ),
        z*x + h*(-w*y - x*y ) 
    );
    Falg / I
)
 X = makeAlgX(h) 



 // Algebra Y
makeAlgY = (h,f) -> (
    kk := QQ;
    Falg  := kk<|x,y,z,w|>;    
    I  := ideal(
        x*w - w*x,
        z*y + y*z,
        y*w + h*(-w*y),
        y*x + h*(-f*w*y + x*y - w*z ),
        z*w + h*(-w*z ),
        z*x + h*(-w*y - f*w*z + x*z )
    );
    Falg / I
)
 Y = makeAlgY(h,f) 



 // Algebra Z
makeAlgZ = (h,f) -> (
    kk := QQ;
    Falg  := kk<|x,y,z,w|>;    
    I  := ideal(
        x*w + w*x,
        z*y - y*z,
        y*w + h*(-w*y - x*z ),
        y*x + h*(-x*y - w*z ),
        z*w + h*(-f*x*y + w*z ),
        z*x + h*(-f*w*y + x*z )
    );
    Falg / I
)
 Z = makeAlgZ(h,f) 



 // Central Extensions 
makeAlgCentExt = (a,b,c,alpha1,alpha2,alpha3,l11,l12,l13,l22,l23,l33) -> (
    kk := QQ;
    Falg  := kk<|x1,x2,x3,x4|>;    
    I  := ideal(
        x1*x4-x4*x1,
        x2*x4-x4*x2,
        x3*x4-x4*x3, 
        c*x1^2 + a*x2*x3 + b*x3*x2 + l11*x1*x4 + l12*x2*x4 + l13*x3*x4 + alpha1*x4^2,
        c*x2^2 + a*x3*x1 + b*x1*x3 + l12*x1*x4 + l22*x2*x4 + l23*x3*x4 + alpha2*x4^2,
        c*x3^2 + a*x1*x2 + b*x2*x1 + l13*x1*x4 + l23*x2*x4 + l33*x3*x4 + alpha3*x4^2
    );
    Falg / I
)
 CentExt = makeAlgCentExt(a,b,c,alpha1,alpha2,alpha3,l11,l12,l13,l22,l23,l33) 



 // Algebra Colin-Brent/ Central Extensions Twist
makeAlgCentExttwist = (q,b,c0,c1,c2) -> (
    kk := QQ;
    Falg  := kk<|x1,x2,x3,x4|>;    
    I  := ideal(
        x2*x1 + q*x1*x2 + b*x4^2 + c0*x3^2,
        x4*x2 + q*x2*x4 + b*x1^2 + c1*x3^2,
        x1*x4 + q*x4*x1 + b*x2^2 + c2*x3^2,
        x4*x3 + x3*x4,
        x1*x3 + x3*x1,
        x2*x3 + x3*x2
    );
    Falg / I
)
 CentExttwist = makeAlgCentExttwist(q,b,c0,c1,c2) 



 // Algebra L(1,1,2)
makeAlgL112 = (p0,p1,lambda) -> (
    kk := QQ;
    Falg  := kk<|x0,x1,x2,x3|>;    
    I  := ideal(
        x1*x0 - x0*x1,
        x2*x0 - p0^(-1)*x0*x2,
        x2*x1 - p1*x1*x2,
        x3*x2 - p0^(-1)*p1*x2*x3 - ((p1 - p0)*(x0^(2) + lambda*x0*x1 + x1^(2)) + (1- p0^(2))*x0^(2) + (p1^(2)-1)*x1^(2)),
        x3*x0 - p0*x0*x3,
        x3*x1 - p1^(-1)*x1*x3
    );
    Falg / I
)
 L112 = makeAlgL112(p0,p1,lambda) 



 // Algebra E(3)
makeAlgE3 = () -> (
    kk := QQ;
    Falg  := kk<|x0,x1,x2,x3|>;    
    I  := ideal(
        x0*x1 - x1*x0 - 5*(x0^2),
        x1*x2 - x2*x1 - 3*x0*x2 - (x1^2) + (3/2)*x0*x1,
        x0*x2 - x2*x0 - 5*x0*x1 + (45/2)*(x0^2),
        x1*x3 - x3*x1 - 7*x0*x3 - x1*x2 + 3*x0*x2 + (5/2)*(x1^2) - 5*x0*x1,
        x0*x3 - x3*x0 - 5*x0*x2 + (45/2)*x0*x1 - (195/2)* (x0^2),
        x2*x3 - x3*x2 - 7*x1*x3 + (77/2)*x0*x3 + 3*(x2^2) - (21/2)*x1*x2 + (77/2)*x0*x2
    );
    Falg / I
)
 E3 = makeAlgE3() 



 // Algebra Sklyanin
makeAlgSklyanin = (alpha,beta) -> (
    kk := QQ;
    Falg  := kk<|x0,x1,x2,x3|>;    
    I  := ideal(
        x0*x1 - x1*x0 - alpha* (x2*x3 + x3*x2),
        x0*x2 - x2*x0 - beta* (x3*x1 + x1*x3),
        x0*x3 - x3*x0 - ((-alpha-beta)/ (1 + alpha*beta)) * (x1*x2 + x2*x1),
        x0*x1 + x1*x0 - (x2*x3 - x3*x2),
        x0*x2 + x2*x0 - (x3*x1 - x1*x3),
        x0*x3 + x3*x0 - (x1*x2 - x2*x1)
    );
    Falg / I
)
 Sklyanin = makeAlgSklyanin(alpha,beta) 



 // Algebra Sklyanin Twist
makeAlgSklyanintwist = (alpha,beta) -> (
    kk := QQ;
    Falg  := kk<|x1,x2,x3,x4|>;    
    I  := ideal(
        x1*x2 - x2*x1 - alpha* (x3*x4 - x4*x3),
        x1*x2 + x2*x1 - (x3*x4 + x4*x3),
        x1*x3 - x3*x1 - beta* (x4*x2 - x2*x4),
        x1*x3 + x3*x1 - (x4*x2 + x2*x4),
        x1*x4 - x4*x1 + ((-alpha-beta)/ (1 + alpha*beta)) * (x2*x3 - x3*x2),
        x1*x4 + x4*x1 + x2*x3 + x3*x2
    );
    Falg / I
)
 Sklyanintwist = makeAlgSklyanintwist(alpha,beta) 



 // Algebra Vancliff
makeAlgVancliff = (alpha,beta,lambda) -> (
    kk := QQ;
    Falg  := kk<|x1,x2,x3,x4|>;    
    I  := ideal(
        x2*x1 - alpha*x1*x2,
        x3*x1 - lambda*x1*x3,
        x4*x1 - alpha*lambda*x1*x4,
        x4*x3 - alpha*x3*x4,
        x4*x2 - lambda*x2*x4,
        x3*x2 - beta*x2*x3 - (alpha*beta - lambda)*x1*x4
    );
    Falg / I
)
 Vancliff = makeAlgVancliff(alpha,beta,lambda) 



 // Algebra Vancliff Twist
makeAlgVanclifftwist = (alpha,beta,lambda) -> (
    kk := QQ;
    Falg  := kk<|x1,x2,x3,x4|>;    
    I  := ideal(
        x2*x1 - alpha*x1*x2,
        x3*x1 - lambda*x1*x3,
        x4*x1 - alpha*lambda*x1*x4,
        x4*x3 + alpha*x3*x4,
        x4*x2 + lambda*x2*x4,
        x3*x2  + beta*x2*x3 - (alpha*beta - lambda)*x1*x4 
    );
    Falg / I
)
 Vanclifftwist = makeAlgVanclifftwist(alpha,beta,lambda) 



 // Algebra Shelton-Tingey
makeAlgSheltonTingey = () -> (
    kk := QQ[p]/(p^2 + 1);   
    Falg  := kk<|x1,x2,x3,x4|>;     
    I  := ideal(
        x3 *x1 - x1*x3 + x2*x2,
        p*x4*x1  + x1*x4,
        x4*x2 - x2*x4 + x3*x3,
        p*x3*x2  + x2*x3,
        x1*x1  - x3*x3,
        x2*x2  - x4*x4  
    );
    Falg / I
)
 SheltonTingey = makeAlgSheltonTingey()



 // Algebra SInfinity
makeAlgSInfinity = (alpha,beta) -> (
    kk := QQ;
    Falg  := kk<|x1,x2,x3,x4|>;    
    I  := ideal(
        x1*x2 - x2*x1 - alpha* (x3*x4 + x4*x3),
        x1*x2 + x2*x1 - (x3*x4 - x4*x3),
        x1*x3 - x3*x1 - beta*(x4*x2 + x2*x4),
        x1*x3 + x3*x1 - (x4*x2 - x2*x4),
        (-1)*x1^(2) + x2^(2) + x3^(2) + x4^(2),
        x2^(2) + ((1 + alpha)/(1 - beta))*x3^(2) + ((1 - alpha)/(1 + ((-alpha-beta)/ (1 + alpha*beta)) ))*x4^(2)
    );
    Falg / I
)
 SInfinity = makeAlgSInfinity(alpha,beta) 



 // Algebra SInfinity Twist
makeAlgSInfinitytwist = (alpha,beta) -> (
    kk := QQ;
    Falg  := kk<|x1,x2,x3,x4|>;    
    I  := ideal(
        x1*x2 - x2*x1 - alpha* (x3*x4 - x4*x3),
        x1*x2 + x2*x1 - (x3*x4 + x4*x3),
        x1*x3 - x3*x1 - beta*(x4*x2 - x2*x4),
        x1*x3 + x3*x1 - (x4*x2 + x2*x4),
        (-1)*x1^(2) + x2^(2) + x3^(2) + (-1)* x4^(2),
        x2^(2) + ((1 + alpha)/(1 - beta))*x3^(2) - ((1 - alpha)/(1 + ((-alpha-beta)/ (1 + alpha*beta)) ))*x4^(2)
    );
    Falg / I
)
 SInfinitytwist = makeAlgSInfinitytwist(alpha,beta) 



 // Algebra S_{d,i=1}
makeAlgSd1 = (alpha,beta,d1,d2) -> (
    kk := QQ;
    Falg  := kk<|x0,x1,x2,x3|>;    
    I  := ideal(
        d1*(-x0^(2) + x1^(2) + x2^(2) + x3^(2)) + d2* (x1^(2) + 
        ((1 + alpha)/ (1 - beta))*x2^(2) + ((1 - alpha)/ (1 + (-alpha-beta)/ (1 + alpha*beta)))*x3^(2) ),
        x0*x1 + x1*x0 - (x2*x3 - x3*x2),
        x0*x2 - x2*x0 - beta* (x3*x1 + x1*x3),
        x0*x3 - x3*x0 - ((-alpha-beta)/ (1 + alpha*beta)) * (x1*x2 + x2*x1),
        x0*x2 + x2*x0 - (x3*x1 - x1*x3),
        x0*x3 + x3*x0 - (x1*x2 - x2*x1)
    );
    Falg / I
)
 Sd1 = makeAlgSd1(alpha,beta,d1,d2) 



 // Algebra S_{d,i=2}
makeAlgSd2 = (alpha,beta,d1,d2) -> (
    kk := QQ;
    Falg  := kk<|x0,x1,x2,x3|>;    
    I  := ideal(
        d1*(-x0^(2) + x1^(2) + x2^(2) + x3^(2)) + d2* (x1^(2) + 
        ((1 + alpha)/ (1 - beta))*x2^(2) + ((1 - alpha)/ (1 + (-alpha-beta)/ (1 + alpha*beta)))*x3^(2) ),
        x0*x1 - x1*x0 - alpha* (x2*x3 + x3*x2),
        x0*x2 - x2*x0 - beta* (x3*x1 + x1*x3),
        x0*x3 - x3*x0 - ((-alpha-beta)/ (1 + alpha*beta)) * (x1*x2 + x2*x1),
        x0*x2 + x2*x0 - (x3*x1 - x1*x3),
        x0*x3 + x3*x0 - (x1*x2 - x2*x1)
    );
    Falg / I
)
 Sd2 = makeAlgSd2(alpha,beta,d1,d2) 



 // Algebra S_{d,i=3}
makeAlgSd3 = (alpha,beta,d1,d2) -> (
    kk := QQ;
    Falg  := kk<|x0,x1,x2,x3|>;    
    I  := ideal(
        d1*(-x0^(2) + x1^(2) + x2^(2) + x3^(2)) + d2* (x1^(2) + 
        ((1 + alpha)/ (1 - beta))*x2^(2) + ((1 - alpha)/ (1 + (-alpha-beta)/ (1 + alpha*beta)))*x3^(2) ),
        x0*x1 - x1*x0 - alpha* (x2*x3 + x3*x2),
        x0*x1 + x1*x0 - (x2*x3 - x3*x2),
        x0*x3 - x3*x0 - ((-alpha-beta)/ (1 + alpha*beta)) * (x1*x2 + x2*x1),
        x0*x2 + x2*x0 - (x3*x1 - x1*x3),
        x0*x3 + x3*x0 - (x1*x2 - x2*x1)
    );
    Falg / I
)
 Sd3 = makeAlgSd3(alpha,beta,d1,d2) 



 // Algebra S_{d,i=4}
makeAlgSd4 = (alpha,beta,d1,d2) -> (
    kk := QQ;
    Falg  := kk<|x0,x1,x2,x3|>;    
    I  := ideal(
        d1*(-x0^(2) + x1^(2) + x2^(2) + x3^(2)) + d2* (x1^(2) + 
        ((1 + alpha)/ (1 - beta))*x2^(2) + ((1 - alpha)/ (1 + (-alpha-beta)/ (1 + alpha*beta)))*x3^(2) ),
        x0*x1 - x1*x0 - alpha* (x2*x3 + x3*x2),
        x0*x2 - x2*x0 - beta* (x3*x1 + x1*x3),
        x0*x3 - x3*x0 - ((-alpha-beta)/ (1 + alpha*beta)) * (x1*x2 + x2*x1),
        x0*x1 + x1*x0 - (x2*x3 - x3*x2),
        x0*x3 + x3*x0 - (x1*x2 - x2*x1)
    );
    Falg / I
)
 Sd4 = makeAlgSd4(alpha,beta,d1,d2) 



 // Algebra S_{d,i=5}
makeAlgSd5 = (alpha,beta,d1,d2) -> (
    kk := QQ;
    Falg  := kk<|x0,x1,x2,x3|>;    
    I  := ideal(
        d1*(-x0^(2) + x1^(2) + x2^(2) + x3^(2)) + d2* (x1^(2) + 
        ((1 + alpha)/ (1 - beta))*x2^(2) + ((1 - alpha)/ (1 + (-alpha-beta)/ (1 + alpha*beta)))*x3^(2) ),
        x0*x1 - x1*x0 - alpha* (x2*x3 + x3*x2),
        x0*x2 - x2*x0 - beta* (x3*x1 + x1*x3),
        x0*x2 + x2*x0 - (x3*x1 - x1*x3),
        x0*x1 + x1*x0 - (x2*x3 - x3*x2),
        x0*x3 + x3*x0 - (x1*x2 - x2*x1)
    );
    Falg / I
)
 Sd5 = makeAlgSd5(alpha,beta,d1,d2) 



 // Algebra S_{d,i=6}
makeAlgSd6 = (alpha,beta,d1,d2) -> (
    kk := QQ;
    Falg  := kk<|x0,x1,x2,x3|>;    
    I  := ideal(
        d1*(-x0^(2) + x1^(2) + x2^(2) + x3^(2)) + d2* (x1^(2) + 
        ((1 + alpha)/ (1 - beta))*x2^(2) + ((1 - alpha)/ (1 + (-alpha-beta)/ (1 + alpha*beta)))*x3^(2) ),
        x0*x1 - x1*x0 - alpha* (x2*x3 + x3*x2),
        x0*x2 - x2*x0 - beta* (x3*x1 + x1*x3),
        x0*x3 - x3*x0 - ((-alpha-beta)/ (1 + alpha*beta)) * (x1*x2 + x2*x1),
        x0*x1 + x1*x0 - (x2*x3 - x3*x2),
        x0*x2 + x2*x0 - (x3*x1 - x1*x3)
    );
    Falg / I
)
 Sd6 = makeAlgSd6(alpha,beta,d1,d2) 



 // Algebra S_{d,i=1} Twist
makeAlgSd1twist = (alpha,beta,d1,d2) -> (
    kk := QQ;
    Falg  := kk<|x0,x1,x2,x3|>;    
    I  := ideal(
        d1*(-x0^(2) + x1^(2) + x2^(2) + (-1)* x3^(2)) + d2* (x1^(2) + 
        ((1 + alpha)/ (1 - beta))*x2^(2) - ((1 - alpha)/ (1 + (-alpha-beta)/ (1 + alpha*beta)))*x3^(2) ),
        x0*x1 + x1*x0 - (x2*x3 + x3*x2),
        x0*x2 - x2*x0 - beta* (x3*x1 - x1*x3),
        x0*x3 - x3*x0 + ((-alpha-beta)/ (1 + alpha*beta)) * (x1*x2 - x2*x1),
        x0*x2 + x2*x0 - (x3*x1 + x1*x3),
        x0*x3 + x3*x0 + (x1*x2 + x2*x1)
    );
    Falg / I
)
 Sd1twist = makeAlgSd1twist(alpha,beta,d1,d2) 



 // Algebra S_{d,i=2} Twist
makeAlgSd2twist = (alpha,beta,d1,d2) -> (
    kk := QQ;
    Falg  := kk<|x0,x1,x2,x3|>;    
    I  := ideal(
        d1*(-x0^(2) + x1^(2) + x2^(2) + (-1)* x3^(2)) + d2* (x1^(2) + 
        ((1 + alpha)/ (1 - beta))*x2^(2) - ((1 - alpha)/ (1 + (-alpha-beta)/ (1 + alpha*beta)))*x3^(2) ),
        x0*x1 - x1*x0 - alpha* (x2*x3 - x3*x2),
        x0*x2 - x2*x0 - beta* (x3*x1 - x1*x3),
        x0*x3 - x3*x0 + ((-alpha-beta)/ (1 + alpha*beta)) * (x1*x2 - x2*x1),
        x0*x2 + x2*x0 - (x3*x1 + x1*x3),
        x0*x3 + x3*x0 + (x1*x2 + x2*x1)
    );
    Falg / I
)
 Sd2twist = makeAlgSd2twist(alpha,beta,d1,d2) 



 // Algebra S_{d,i=3} Twist
makeAlgSd3twist = (alpha,beta,d1,d2) -> (
    kk := QQ;
    Falg  := kk<|x0,x1,x2,x3|>;    
    I  := ideal(
        d1*(-x0^(2) + x1^(2) + x2^(2) + (-1)* x3^(2)) + d2* (x1^(2) + 
        ((1 + alpha)/ (1 - beta))*x2^(2) - ((1 - alpha)/ (1 + (-alpha-beta)/ (1 + alpha*beta)))*x3^(2) ),
        x0*x1 - x1*x0 - alpha* (x2*x3 - x3*x2),
        x0*x1 + x1*x0 - (x2*x3 + x3*x2),
        x0*x3 - x3*x0 + ((-alpha-beta)/ (1 + alpha*beta)) * (x1*x2 - x2*x1),
        x0*x2 + x2*x0 - (x3*x1 + x1*x3),
        x0*x3 + x3*x0 + (x1*x2 + x2*x1)
    );
    Falg / I
)
 Sd3twist = makeAlgSd3twist(alpha,beta,d1,d2) 



 // Algebra S_{d,i=4} Twist
makeAlgSd4twist = (alpha,beta,d1,d2) -> (
    kk := QQ;
    Falg  := kk<|x0,x1,x2,x3|>;    
    I  := ideal(
        d1*(-x0^(2) + x1^(2) + x2^(2) + (-1)* x3^(2)) + d2* (x1^(2) + 
        ((1 + alpha)/ (1 - beta))*x2^(2) - ((1 - alpha)/ (1 + (-alpha-beta)/ (1 + alpha*beta)))*x3^(2) ),
        x0*x1 - x1*x0 - alpha* (x2*x3 - x3*x2),
        x0*x2 - x2*x0 - beta* (x3*x1 - x1*x3),
        x0*x3 - x3*x0 + ((-alpha-beta)/ (1 + alpha*beta)) * (x1*x2 - x2*x1),
        x0*x1 + x1*x0 - (x2*x3 + x3*x2),
        x0*x3 + x3*x0 + (x1*x2 + x2*x1)
    );
    Falg / I
)
 Sd4twist = makeAlgSd4twist(alpha,beta,d1,d2) 



 // Algebra S_{d,i=5} Twist
makeAlgSd5twist = (alpha,beta,d1,d2) -> (
    kk := QQ;
    Falg  := kk<|x0,x1,x2,x3|>;    
    I  := ideal(
        d1*(-x0^(2) + x1^(2) + x2^(2) + (-1)* x3^(2)) + d2* (x1^(2) + 
        ((1 + alpha)/ (1 - beta))*x2^(2) - ((1 - alpha)/ (1 + (-alpha-beta)/ (1 + alpha*beta)))*x3^(2) ),
        x0*x1 - x1*x0 - alpha* (x2*x3 - x3*x2),
        x0*x2 - x2*x0 - beta* (x3*x1 - x1*x3),
        x0*x1 + x1*x0 -  (x2*x3 + x3*x2),
        x0*x2 + x2*x0 - (x3*x1 + x1*x3),
        x0*x3 + x3*x0 + (x1*x2 + x2*x1)
    );
    Falg / I
)
 Sd5twist = makeAlgSd5twist(alpha,beta,d1,d2) 



 // Algebra S_{d,i=6} Twist
makeAlgSd6twist = (alpha,beta,d1,d2) -> (
    kk := QQ;
    Falg  := kk<|x0,x1,x2,x3|>;    
    I  := ideal(
        d1*(-x0^(2) + x1^(2) + x2^(2) + (-1)* x3^(2)) + d2* (x1^(2) + 
        ((1 + alpha)/ (1 - beta))*x2^(2) - ((1 - alpha)/ (1 + (-alpha-beta)/ (1 + alpha*beta)))*x3^(2) ),
        x0*x1 - x1*x0 - alpha* (x2*x3 - x3*x2),
        x0*x2 - x2*x0 - beta* (x3*x1 - x1*x3),
        x0*x3 - x3*x0 + ((-alpha-beta)/ (1 + alpha*beta)) * (x1*x2 - x2*x1),
        x0*x2 + x2*x0 - (x3*x1 + x1*x3),
        x0*x1 + x1*x0 - (x2*x3 + x3*x2)
    );
    Falg / I
)
 Sd6twist = makeAlgSd6twist(alpha,beta,d1,d2) 



 // Algebra Polynomial Ring
makeAlgPolyRing = () -> (
    kk := QQ;
    Falg  := kk<|x1,x2,x3,x4|>;    
    I  := ideal(
        x1*x2 - x2*x1,
        x1*x3 - x3*x1,
        x1*x4 - x4*x1,
        x2*x3 - x3*x2,
        x2*x4 - x4*x2,
        x3*x4 - x4*x3
    );
    Falg / I
)
 PolyRing = makeAlgPolyRing() 



 // Algebra Skew Polynomial Ring or Algebra Tetrahedron
makeAlgskewPolyRing = (q12,q13,q14,q23,q24,q34) -> (
    kk := QQ;
    Falg  := kk<|x1,x2,x3,x4|>;    
    I  := ideal(
        x1*x2 - q12*x2*x1,
        x1*x3 - q13*x3*x1,
        x1*x4 - q14*x4*x1,
        x2*x3 - q23*x3*x2,
        x2*x4 - q24*x4*x2,
        x3*x4 - q34*x4*x3
    );
    Falg / I
)
 skewPolyRing = makeAlgskewPolyRing(q12,q13,q14,q23,q24,q34) 



 // Algebra Clifford
makeAlgClifford = () -> (
    kk := QQ;
    Falg  := kk<|x1,x2,x3,x4|>;    
    I  := ideal(
        x1*x2 + x2*x1 + 2*x1^2 + 3*x2^2 + 4*x3^2 + 5*x4^2,
        x1*x3 + x3*x1 + (7)*x1^2 + (-10)*x2^2 + (7)*x3^2 + (8)*x4^2,
        x1*x4 + x4*x1 + (9)*x1^2 + (7)*x2^2 + (-3)*x3^2 + (-2)*x4^2,
        x2*x3 + x3*x2 + (-1)*x1^2 + (6)*x2^2 + (8)*x3^2 + (2)*x4^2,
        x2*x4 + x4*x2 + (1)*x1^2 + (1)*x2^2 + (6)*x3^2 + (3)*x4^2,
        x3*x4 + x4*x3 + (7)*x1^2 + (-1)*x2^2 + (4)*x3^2 + (5)*x4^2
    );
    Falg / I
)
 Clifford = makeAlgClifford() 



 // Algebra S(2,3)
makeAlgStwothree = (b1,b2,b3,d1,d2,d3) -> (
    kk := QQ;
    Falg  := kk<|x0,x1,x2,x3|>;    
    I  := ideal(
        x0*x1 - x1*x0 - x1^(2) - x1*(b1*x2+(-2-b2)*x3) - d1*x2*x3,
        x0*x2 - x2*x0 - x2^(2) - x2*(b2*x3+(-2-b3)*x1) - d2*x3*x1,
        x0*x3 - x3*x0 - x3^(2) - x3*(b3*x1+(-2-b1)*x2) - d3*x1*x2,
        x2*x3 - x3*x2,
        x3*x1 -x1*x3,
        x1*x2 - x2*x1
    );
    Falg / I
)
 Stwothree = makeAlgStwothree(b1,b2,b3,d1,d2,d3) 



 // Algebra Kirkman R
makeAlgKirkmanR = () -> (
    kk := QQ;
    Falg  := kk<|x1,x2,x3,x4|>;    
    I  := ideal(
        x1*x2 + x2*x1,
        x1*x3 + x4*x2,
        x1*x4 - x3*x2,
        x2*x3 - x4*x1,
        x2*x4 + x3*x1,
        x3*x4 + x4*x3
    );
    Falg / I
)
 KirkmanR = makeAlgKirkmanR() 



 // Algebra Kirkman S
makeAlgKirkmanS = () -> (
    kk := QQ;
    Falg  := kk<|x1,x2,x3,x4|>;    
    I  := ideal(
        x1*x2 - x3*x3,
        x1*x3 - x2*x4,
        x1*x4 - x4*x2,
        x2*x3 - x3*x1,
        x3*x2 - x4*x1,
        x2*x1 - x4*x4
    );
    Falg / I
)
 KirkmanS = makeAlgKirkmanS() 



 // Algebra Kirkman T
makeAlgKirkmanT = () -> (
    kk := QQ;
    Falg  := kk<|x1,x2,x3,x4|>;    
    I  := ideal(
        x1*x2 - x3*x3,
        x1*x3 - x2*x4,
        x1*x4 + x4*x2,
        x2*x3 - x3*x1,
        x3*x2 - x4*x1,
        x2*x1 + x4*x4
    );
    Falg / I
)
 KirkmanT = makeAlgKirkmanT() 



 // Algebra Cassidy-Vancliff 1
makeAlgCassidyVancliff1 = (gamma) -> (
    kk := QQ[p,q]/(p^2 + 1, q^2+1);   
    Falg  := kk<|x1,x2,x3,x4|>;    
    I  := ideal(
        x4*x1 - p*x1*x4,
        x3*x2 - q*x2*x3,
        x3*x3 - x1*x1,
        x4*x4 - x2*x2,
        x3*x1 - x1*x3 + x2*x2,
        x4*x2 - x2*x4 + gamma^2*x1^2
    );
    Falg / I
)
 CassidyVancliff1 = makeAlgCassidyVancliff1(gamma)



 // Algebra Cassidy-Vancliff 2
makeAlgCassidyVancliff2 = (alpha1,alpha2,beta1,beta2) -> (
    kk := QQ;   
    Falg  := kk<|x1,x2,x3,x4|>;    
    I  := ideal(
        x3*x1 + x1*x3 - beta2*x2^2,
        x4*x1 + x1*x4 - alpha2*x3^2,
        x2*x3 - x3*x2,
        x4*x4 - x2*x2,
        x4*x2 + x2*x4 - x3^2,
        alpha1*x3^2 + beta1*x2^2 - x1^2
    );
    Falg / I
)
 CassidyVancliff2 = makeAlgCassidyVancliff2(alpha1,alpha2,beta1,beta2)



 // Algebra Cassidy-Vancliff 3 (Consider u13=-1, u14=-1, u34 =1, u24=1 for simplification)
makeAlgCassidyVancliff3 = (u13,u14,u34,u24) -> (
    kk := QQ;   
    Falg  := kk<|x1,x2,x3,x4|>;    
    I  := ideal(
        x1*x3 + u13*x3*x1,
        x1*x4 + u14*x4*x1,
        x3*x4 + u34*x4*x3,
        x4*x4 - x2*x2,
        x2*x3 + x3*x2 + x4^2,
        x2*x4 + u24*x4*x2 + x1^2
    );
    Falg / I
)
 CassidyVancliff3 = makeAlgCassidyVancliff3(u13,u14,u34,u24)



 // Algebra A5
makeAlgA5 = (a1,a4,a7,d) -> (
    kk := QQ[p]/(p^2 + 1);   
    Falg  := kk<|x1,x2,x3,x4|>;    
    I  := ideal(
        d*x1*x4 + x4*x1,
        d*x2*x4 - x4*x2,
        a1*x1^2 + a4*d^2*x2^2,
        d*x3*x4 - p*x4*x3,
        a4*x1*x2 + a4*x2*x1 - a7*x3^2,
        x2*x3 + x3*x2 
    );
    Falg / I
)
 A5 = makeAlgA5(a1,a4,a7,d)



 // Caines Algebra 
makeAlgCaines = (a,b,c,d) -> (
    kk := QQ;   
    Falg  := kk<|x1,x2,x3,x4|>;    
    I  := ideal(
        x4*x3 - x3*x4 - a*x1*x2,
        x4*x2 - b*x3^2 + x2*x4,
        x4*x1 - c*x3^2 + x1*x4,
        x3*x2 - x2*x3 + (b*d/c)*x2*x4 - (b^2*d/c^2)*x1*x4,
        x3*x1 - x1*x3 + (b*d/c)*x1*x4 - d*x2*x4,
        x2*x1 + x1*x2
    );
    Falg / I
)
 CainesAlgebra = makeAlgCaines(a,b,c,d)



 // Algebra F(0,-1,-1,2)(0,0,0,0)
makeAlgF1 = (q14, q13, q23, q24, t) -> (
    kk := QQ;   
    Falg  := kk<|x1,x2,x3,x4|>;    
    I  := ideal(
        x2*x1 - (q14^2 / q13)*x1*x2,
        x3*x1 - q13*x1*x3,
        x4*x1 - q14*x1*x4,
        x3*x2 - q23*x2*x3 - t*x4*x4,
        x4*x2 - q24*x2*x4,
        x4*x3 - (1/q24)*x3*x4
    );
    Falg / I
)
 AlgebraF1 = makeAlgF1(q14, q13, q23, q24, t)



 // Algebra F(-1,-1,1,1)(0,0,0,0)
makeAlgF2 = (q12, t, q13, q14, q23) -> (
    kk := QQ;   
    Falg  := kk<|x1,x2,x3,x4|>;    
    I  := ideal(
        x2*x1 - q12*x1*x2 - t*x3*x4,
        x3*x1 - q13*x1*x3,
        x4*x1 - q14*x1*x4,
        x3*x2 - q23*x2*x3,
        x4*x2 - (1/(q13*q23*q14))*x2*x4,
        x4*x3 - (1/(q13*q23))*x3*x4 
    );
    Falg / I
)
 AlgebraF2 = makeAlgF2(q12, t, q13, q14, q23)



 // Algebra F(0,-1,-1,2)(0,0,0,0)(2,-1,-1,0)
makeAlgF3 = (q13, q23, t, s, q34) -> (
    kk := QQ;   
    Falg  := kk<|x1,x2,x3,x4|>;    
    I  := ideal(
        x2*x1 - (1/q13)*x1*x2,
        x3*x1 - q13*x1*x3,
        x4*x1 - x1*x4,
        x3*x2 - q23*x2*x3 - t*x4*x4 - s*x1*x1,
        x4*x2 - (1/q34)*x2*x4,
        x4*x3 - q34*x3*x4
    );
    Falg / I
)
 AlgebraF3 = makeAlgF3(q13, q23, t, s, q34)



 // Algebra F(0,-1,-1,2)(-1,0,-1,2)(0,0,0,0)
makeAlgF4 = (q12, q14, t, s) -> (
    kk := QQ;   
    Falg  := kk<|x1,x2,x3,x4|>;    
    I  := ideal(
        x2*x1 - q12*x1*x2,
        x3*x1 - (q14^2 / q12)*x1*x3 - t*x4*x4,
        x4*x1 - q14*x1*x4,
        x3*x2 - (q14^2 * q12)*x2*x3 - s*x4*x4,
        x4*x2 - q14*x2*x4,
        x4*x3 - (1/q14)*x3*x4 
    );
    Falg / I
)
 AlgebraF4 = makeAlgF4(q12, q14, t, s)



 // Algebra F(0,-1,-1,2)(0,0,0,0)(-1,-1,2,0)
makeAlgF5 = (q12, t, q24, s) -> (
    kk := QQ;   
    Falg  := kk<|x1,x2,x3,x4|>;    
    I  := ideal(
        x2*x1 - q12*x1*x2 - t*x3*x3,
        x3*x1 - (1 / (q24^6 * q12))*x1*x3,
        x4*x1 - (1 / q24^3)*x1*x4,
        x3*x2 - (q24^6 * q12)*x2*x3 - s*x4*x4,
        x4*x2 - q24*x2*x4,
        x4*x3 - (1 / q24)*x3*x4
    );
    Falg / I
)
 AlgebraF5 = makeAlgF5(q12, t, q24, s)



 // Algebra R(3,a)
makeAlgR3a = (a) -> (
    kk := QQ;   
    Falg  := kk<|x1,x2,x3,x4|>;    
    I  := ideal(
        x4*x1 - x1*x4 + 4*a*x4^2,
        x1*x2 - x2*x1 + 4*(a+1)*x1^2 - 8*(a+1)*(a+2)*x4*x1 - 4*(a+2)*x4*x2,
        x4*x2 - x2*x4  + 4*a*x4*x1  + 8*a^2*x4^2  - 8*a*x4^2,
        x1*x3 - x3*x1 + 4*(a+1)*x1*x2 + 8*a*(a+1)*x1^2 - (64/3)*a*(a+1)*(a+2)*x4*x1 - 16*(a+1)*(a+2)*x4*x2 - 4*(a+3)*x4*x3,
        x4*x3 - x3*x4 + 4*a*x4*x2 - 8*(a - a^2)*x4*x1 - (64/6)*(-a^3 + 3*a^2 - 2*a)*x4^2,
        x2*x3 - x3*x2 + 4*(a+2)*x2^2 - 8*(a+2)*(a+3)*x1*x2  + (64/6)*(a+2)*(a+3)*(a+4)*x4*x2  - 4*(a+3)*x1*x3 + 8*(a+3)*(a+4)*x4*x3 
    );
    Falg / I
)
 R3a = makeAlgR3a(a)



 // Algebra L(1,1,2)^sigma
makeAlgL112sigma = (p0, p1, lambda, alpha, beta) -> (
    kk := QQ;   
    Falg  := kk<|x1,x2,x3,x4|>;    
    I  := ideal(
        alpha*(x2*x1 - x1*x2),
        beta*x3*x1 - (1/p0)*alpha*x1*x3,
        (alpha^2/beta)*x4*x1 - p0*alpha*x1*x4,
        beta*x3*x2 - p1*alpha*x2*x3,
        (alpha^2/beta)*x4*x2 - (1/p1)*alpha*x2*x4,
        (alpha^2/beta)*x4*x3 - p1*(1/p0)*beta*x3*x4 - alpha*(p1 - p0)*(x1^2 + lambda*x1*x2 + x2^2) - alpha*(1 - p0^2)*x1^2 - alpha*(p1^2 - 1)*x2^2
    );
    Falg / I
)
 L112sigma = makeAlgL112sigma(p0, p1, lambda, alpha, beta)



 // Algebra S(2,3)^sigma
makeAlgS23sigma = (c1, c2, c3, d1, d2, d3, alpha, beta1, beta2, beta3) -> (
    kk := QQ;   
    Falg  := kk<|x1,x2,x3,x4|>;    
    I  := ideal(
    alpha*(x4*x1 - x1*x4) 
        + beta1*x1^2 
        + beta2*x2*x1 
        + beta3*x3*x1 
        - alpha*x1^2 
        - alpha*x1*((-c3 - 2)*x2 + c1*x3) 
        - d1*alpha*x2*x3,

    alpha*(x4*x2 - x2*x4) 
        + beta1*x1*x2 
        + beta2*x2^2 
        + beta3*x3*x2 
        - alpha*x2^2 
        - alpha*x2*((-c1 - 2)*x3 + c2*x1) 
        - d2*alpha*x3*x1,

    alpha*(x4*x3 - x3*x4) 
        + beta1*x1*x3 
        + beta2*x2*x3 
        + beta3*x3^2 
        - alpha*x3^2 
        - alpha*x3*((-c2 - 2)*x1 + c3*x2) 
        - d3*alpha*x1*x2,

    x2*x3 - x3*x2,

    x3*x1 - x1*x3,

    x1*x2 - x2*x1
        
    );
    Falg / I
)
 S23sigma = makeAlgS23sigma(c1, c2, c3, d1, d2, d3, alpha, beta1, beta2, beta3)




 // Lie Algebra 1
makeLieAlg1 = () -> (
    kk := QQ;   
    Falg  := kk<|x1,x2,x3,x4|>;    
    I  := ideal(
        x2*x3 - x3*x2 - x1*x4,
        x1*x2 - x2*x1,
        x1*x3 - x3*x1,
        x1*x4 - x4*x1,
        x2*x4 - x4*x2,
        x3*x4 - x4*x3
    );
    Falg / I
)
 LieAlgebra1 = makeLieAlg1()



 // Lie Algebra 2
makeLieAlg2 = () -> (
    kk := QQ;   
    Falg  := kk<|x1,x2,x3,x4|>;    
    I  := ideal(
        x1*x2 - x2*x1 - x1*x4,
        x1*x3 - x3*x1,
        x2*x3 - x3*x2,
        x1*x4 - x4*x1,
        x2*x4 - x4*x2,
        x3*x4 - x4*x3
    );
    Falg / I
)
 LieAlgebra2 = makeLieAlg2()



 // Lie Algebra 3
makeLieAlg3 = (alpha) -> (
    kk := QQ;   
    Falg  := kk<|x1,x2,x3,x4|>;    
    I  := ideal(
        x1*x2 - x2*x1,
        x1*x3 - x3*x1 - x1*x4,
        x2*x3 - x3*x2 - alpha*x2*x4,
        x1*x4 - x4*x1,
        x2*x4 - x4*x2,
        x3*x4 - x4*x3
    );
    Falg / I
)
 LieAlgebra3 = makeLieAlg3(alpha)



 // Lie Algebra 4
makeLieAlg4 = (beta) -> (
    kk := QQ;   
    Falg  := kk<|x1,x2,x3,x4|>;    
    I  := ideal(
        x1*x2 - x2*x1,
        x1*x3 - x3*x1 - x1*x4 - beta*x2*x4,
        x2*x3 - x3*x2 - x2*x4,
        x1*x4 - x4*x1,
        x2*x4 - x4*x2,
        x3*x4 - x4*x3
    );
    Falg / I
)
 LieAlgebra4 = makeLieAlg4(beta)



 // Lie Algebra sl2
makeLieAlgsl2 = () -> (
    kk := QQ;   
    Falg  := kk<|x1,x2,x3,x4|>;    
    I  := ideal(
        x1*x3 - x3*x1 - 2*x1*x4,
        x2*x3 - x3*x2 + 2*x2*x4,
        x1*x2 - x2*x1 - x3*x4,
        x1*x4 - x4*x1,
        x2*x4 - x4*x2,
        x3*x4 - x4*x3
    );
    Falg / I
)
 LieAlgebrasl2 = makeLieAlgsl2() 



 // Algebra OreExt. TypeA1
makeAlgOreExtTypeA1 = (a,b,c,d) -> (
    kk := QQ[p]/(p^2 + p + 1);         -- p is a primitive 3rd root of unity
    Falg  := kk<|x1,x2,x3,x4|>;    
    I  := ideal(
        c*x1^2 + a*x2*x3 + b*x3*x2,
        c*x2^2 + a*x3*x1 + b*x1*x3,
        c*x3^2 + a*x1*x2 + b*x2*x1,
        x4*x1 - d*x1*x4,
        x4*x2 - d*p*x2*x4,
        x4*x3 - d*p^2*x3*x4 
    );
    Falg / I
)
 OreExtTypeA1 = makeAlgOreExtTypeA1(a,b,c,d) 



 // Algebra OreExt. TypeA2
makeAlgOreExtTypeA2 = (a,b,c,d) -> (
    kk := QQ[p]/(p^2 + p + 1);       -- p is a primitive 3rd root of unity
    Falg  := kk<|x1,x2,x3,x4|>;    
    I  := ideal(
        c*x1^2 + a*x2*x3 + b*x3*x2,
        c*x2^2 + a*x3*x1 + b*x1*x3,
        c*x3^2 + a*x1*x2 + b*x2*x1,
        x4*x1 - d*x2*x4,
        x4*x2 - d*p*x3*x4,
        x4*x3 - d*p^2*x1*x4
    );
    Falg / I
)
 OreExtTypeA2 = makeAlgOreExtTypeA2(a,b,c,d) 



 // Algebra OreExt. TypeA3
makeAlgOreExtTypeA3 = (a,b,c,d) -> (
    kk := QQ[p]/(p^2 + p + 1);        -- p is a primitive 3rd root of unity
    Falg  := kk<|x1,x2,x3,x4|>;    
    I  := ideal(
        c*x1^2 + a*x2*x3 + b*x3*x2,
        c*x2^2 + a*x3*x1 + b*x1*x3,
        c*x3^2 + a*x1*x2 + b*x2*x1,
        x4*x1 - d*x3*x4,
        x4*x2 - d*p*x1*x4,
        x4*x3 - d*p^2*x2*x4
    );
    Falg / I
)
 OreExtTypeA3 = makeAlgOreExtTypeA3(a,b,c,d) 



 // Algebra OreExt. TypeB1
makeAlgOreExtTypeB1 = (a,d,alpha) -> (
    kk := QQ[p]/(p + 1);                     -- p is a primitive 2nd root of unity
    Falg  := kk<|x1,x2,x3,x4|>;    
    I  := ideal(
        x1*x2 + x2*x1 + x2^2 - x3^2,
        x1^2 + x2*x1 + x1*x2 - a*x3^2,
        x3*x1 - x1*x3 + a*x3*x2 - a*x2*x3,
        x4*x1 - d*x1*x4,
        x4*x2 - d*x2*x4,
        x4*x3 - p*d*x3*x4
    );
    Falg / I
)
 OreExtTypeB1 = makeAlgOreExtTypeB1(a,d,alpha) 



 // Algebra OreExt. TypeE1
makeAlgOreExtTypeE1 = (a,d) -> (
    kk := QQ[p]/(p^6 + p^3 + 1);         -- p is a primitive 9th root of unity
    Falg  := kk<|x1,x2,x3,x4|>;    
    I  := ideal(
        x3*x1 + p^8*x1*x3 + p^4*x2^2,
        x1*x2 + p^5*x2*x1 + p^7*x3^2,
        p*x1^2 + x2*x3 + p^2*x3*x2,
        x4*x1 - d*x1*x4,
        x4*x2 - d*x2*x4,
        x4*x3 - d*x3*x4
    );
    Falg / I
)
 OreExtTypeE1 = makeAlgOreExtTypeE1(a,d) 



 // Algebra OreExt. TypeE2 
makeAlgOreExtTypeE2 = (a,d) -> (
    kk := QQ[p]/(p^6 + p^3 + 1);        -- p is a primitive 9th root of unity
    Falg  := kk<|x1,x2,x3,x4|>;    
    I  := ideal(
        x3*x1 + p^8*x1*x3 + p^4*x2^2,
        x1*x2 + p^5*x2*x1 + p^7*x3^2,
        p*x1^2 + x2*x3 + p^2*x3*x2,
        x4*x1 - d*x1*x4,
        x4*x2 - d*p^3*x2*x4,
        x4*x3 - d*p^6*x3*x4 
    );
    Falg / I
)
 OreExtTypeE2 = makeAlgOreExtTypeE2(a,d) 



 // Algebra OreExt. TypeH.I
makeAlgOreExtTypeHI = (d) -> (
    kk := QQ[p,i]/(p^2 + 1, i^2+1);        -- p is a primitive 4th root of unity
    Falg  := kk<|x1,x2,x3,x4|>;    
    I  := ideal(
        x1^2 - x2^2,
        x1*x2 - x2*x1 + p*x3^2,
        x2*x3 - p*x3*x2,
        x4*x1 - d*x1*x4,
        x4*x2 + d*x2*x4,
        x4*x3 - i*d*x3*x4
    );
    Falg / I
)
 OreExtTypeHI = makeAlgOreExtTypeHI(d) 



 // Algebra OreExt. TypeH.II
makeAlgOreExtTypeHII = (d) -> (
    kk := QQ[p,i]/(p^2 + 1, i^2+1);        -- p is a primitive 4th root of unity
    Falg  := kk<|x1,x2,x3,x4|>;    
    I  := ideal(
        x1^2 - x2^2,
        x1*x2 - x2*x1 + p*x3^2,
        x2*x3 - p*x3*x2,
        x4*x1 - d*x1*x4,
        x4*x2 - d*x2*x4,
        x4*x3 + d*x3*x4
    );
    Falg / I
)
 OreExtTypeHII = makeAlgOreExtTypeHII(d) 



 // Algebra OreExt. TypeS1^{'}
makeAlgOreExtTypeS1dash = (a,b,c,d,alpha) -> (
    kk := QQ;        
    Falg  := kk<|x1,x2,x3,x4|>;    
    I  := ideal(
        x2*x3 + a*alpha^-1*x3*x2,
        alpha*x3*x1 + a*x1*x3,
        x3^2 + x1*x2 + a*x2*x1,
        x4*x1 - b^2*d*x1*x4,
        x4*x2 - c^2*d*x2*x4,
        x4*x3 - b*c*d*x3*x4 
    );
    Falg / I
)
 OreExtTypeS1dash = makeAlgOreExtTypeS1dash(a,b,c,d,alpha) 



 // Algebra OreExt. TypeS2
makeAlgOreExtTypeS2 = (a,d,alpha) -> (
    kk := QQ[p]/(p + 1);                     -- p is a primitive 2nd root of unity
    Falg  := kk<|x1,x2,x3,x4|>;    
    I  := ideal(
        x3*x1 + alpha^-1*x1*x3,
        x3*x2 - alpha^-1*x2*x3,
        x1^2 - x2^2,
        x4*x1 - a*d*x1*x4,
        x4*x2 - p*a*d*x2*x4,
        x4*x3 - d*x3*x4 
    );
    Falg / I
)
 OreExtTypeS2 = makeAlgOreExtTypeS2(a,d,alpha) 



 // Algebra CentExt. TypeB
makeAlgCentExtTypeB = (a, l11, l12, l22) -> (
    kk := QQ;        
    Falg  := kk<|x1,x2,x3,x4|>;    
    I  := ideal(
        x1*x2 + x2*x1 + x2^2 - x3^2 + (l11*x1 + l12*x2)*x4,
        x1^2 + x2*x1 + x1*x2 - a*x3^2 + (l12*x1 + l22*x2)*x4,
        x3*x1 - x1*x3 + a*x3*x2 - a*x2*x3,
        x4*x1 - x1*x4,
        x4*x2 - x2*x4,
        x4*x3 - x3*x4
    );
    Falg / I
)
 CentExtTypeB = makeAlgCentExtTypeB(a, l11, l12, l22) 



 // Algebra CentExt. TypeE
makeAlgCentExtTypeE = () -> (
    kk := QQ[p]/(p^6 + p^3 + 1);        -- p is a primitive 9th root of unity
    Falg  := kk<|x1,x2,x3,x4|>;    
    I  := ideal(
        x3*x1 + p^8*x1*x3 + p^4*x2^2,
        x1*x2 + p^5*x2*x1 + p^7*x3^2,
        p*x1^2 + x2*x3 + p^2*x3*x2,
        x4*x1 - x1*x4,
        x4*x2 - x2*x4,
        x4*x3 - x3*x4
    );
    Falg / I
)
 CentExtTypeE = makeAlgCentExtTypeE() 



 // Algebra CentExt. TypeH
makeAlgCentExtTypeH = () -> (
   kk := QQ[p]/(p^2 + 1);        -- p is a primitive 4th root of unity
    Falg  := kk<|x1,x2,x3,x4|>;    
    I  := ideal(
        x1^2 - x2^2 + x1*x4,
        x1*x2 - x2*x1 + p*x3^2,
        x2*x3 - p*x3*x2,
        x4*x1 - x1*x4,
        x4*x2 - x2*x4,
        x4*x3 - x3*x4  
    );
    Falg / I
)
CentExtTypeH = makeAlgCentExtTypeH() 



 // Algebra CentExt. TypeS1
makeAlgCentExtTypeS1 = (a, alpha, beta) -> (
    kk := QQ; 
    Falg  := kk<|x1,x2,x3,x4|>;    
    I  := ideal(
        x2*x3 + a*beta*x3*x2,
        alpha*x3*x1 + a*x1*x3,
        x1*x2 + a*x2*x1,
        x4*x1 - x1*x4,
        x4*x2 - x2*x4,
        x4*x3 - x3*x4      
    );
    Falg / I
)
CentExtTypeS1 = makeAlgCentExtTypeS1(a, alpha, beta) 



 // Algebra CentExt. TypeS1^{'}
makeAlgCentExtTypeS1dash = (a, alpha) -> (
    kk := QQ; 
    Falg  := kk<|x1,x2,x3,x4|>;    
    I  := ideal(
        x2*x3 + a*alpha^-1*x3*x2,
        alpha*x3*x1 + a*x1*x3,
        x3^2 + x1*x2 + a*x2*x1,
        x4*x1 - x1*x4,
        x4*x2 - x2*x4,
        x4*x3 - x3*x4     
    );
    Falg / I
)
CentExtTypeS1dash = makeAlgCentExtTypeS1dash(a, alpha) 



 // Algebra CentExt. TypeS2
makeAlgCentExtTypeS2 = (alpha) -> (
    kk := QQ; 
    Falg  := kk<|x1,x2,x3,x4|>;    
    I  := ideal(
        x3*x1 + alpha^-1*x1*x3,
        x3*x2 - alpha^-1*x2*x3,
        x1^2 - x2^2,
        x4*x1 - x1*x4,
        x4*x2 - x2*x4,
        x4*x3 - x3*x4   
    );
    Falg / I
)
CentExtTypeS2 = makeAlgCentExtTypeS2(alpha) 



























 
























 













































