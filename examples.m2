-- given a variety in Projective n space P^n cut out by some 
-- equations x^3+y^3+z^3, or w*x-y*z,w*x+2*y^2
-- analyze it geometrically

kk=QQ -- Rational field
S=kk[x,y,z]
f = x^3+y^3+z^3 --irreducible
I = ideal f
dim I -- dimension of ring R/I -- curve in P2
degree I -- degree of the curve 
si = ideal singularLocus I
dim si -- smooth

restart
k=QQ
S = k[w,x,y,z]
I = ideal(w*x-y*z,w*x+2*y^2)
dim I -- curve
degree I -- degree 4
genus I -- genus 1, not elliptic curve
dim ideal singularLocus I -- singular at points
primaryDecomposition I -- variety is two lines and a conic
radsi = radical ideal singularLocus I
degree radsi -- singular at 3 points
dim radsi
primaryDecomposition radsi
-- variety is singular at 3 points
-- where do the three curves meet each other?

primaryDecomposition ideal (x*y)
--primaryDecompostion ideals <--> variety as union of irred components
-- Macaulay 2 

