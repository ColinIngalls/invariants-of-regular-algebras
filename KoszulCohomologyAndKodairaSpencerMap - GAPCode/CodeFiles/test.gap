Q:=Quiver([[0,3,0],[0,0,3],[0,0,0]]);
kQ:=PathAlgebra(Rationals,Q);
AssignGeneratorVariables(kQ);
x1:=a1;
y1:=a2;
z1:=a3;
x2:=a4;
y2:=a5;
z2:=a6:
relations:=[x1*y2-y1*x2,];
VerticesOfQuiver(Q);
ArrowsOfQuiver(Q);
