restart
kk=ZZ/32771
S = kk[s_0..s_5,a_(0,0,0)..a_(3,3,5),b_(0,0,0)..b_(3,3,5)]
affa = (0..5)/(i->(a_(0,0,i)-1))
affb = (0..5)/(i->(b_(0,0,i)-1))
affs = (s_0-1)
eqns = apply( (0,0,0,0)..(3,3,3,3), (i,j,m,n) -> sum(0..5,k->(s_k*a_(i,j,k)*b_(m,n,k) + s_k*a_(n,i,k)*b_(j,m,k))));

#eqns
I = ideal eqns + ideal affa + ideal affb + ideal affs;

--198 - 13 = 185 affine open

dim S

slice = ideal ( (0..165)/(i->(random(1,S)-random(kk))));



dim slice
degree slice

IS =I+slice;
dim(IS)
degree(IS)


ISS = saturate IS
pd = primaryDecomposition ISS
#pd
