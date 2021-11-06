
#nTensorProduct:= function( V, n )
#  local L, i, TProd ;
#  L:= [ ];
#  for i in [1..n] do
#    Add( L, V );
#  od;
#  TProd:= TensorProduct( L );
#  return TProd ;
#end;


#################################################################################################################################################

#This section is an attempt to code a generic Kodaira-Spencer map

ExtendParametrizedAlgebra:= function( kQ, rels )  #This function inputs the a free algebra over a function field with indeterminates t1, ..., tm,
                                                  #i.e. a parametrized family of algebras, and a finite list of relations rels, and outputs the
                                                  #free algebra over the function field with indeterminates t1, ..., tm, dt1, ..., dtm, with the
                                                  #relations in rels translated over to the new algebra.
  local R, k, indets, ExtendedIndets, t, dt, NewIndets, ExtendedR, ExtendedkQ, kQfam, Extendedfam, Extendedrels, r, rep ;
  R:= LeftActingDomain( kQ );
  k:= LeftActingDomain( R );
  indets:= IndeterminatesOfFunctionField( R );
  ExtendedIndets:= ShallowCopy( indets );
  for t in indets do
    dt:= X( k, StringFormatted( "d{}", t ) ) ;
    Add( ExtendedIndets, dt );
  od;
  ExtendedR:= FunctionField( k, ExtendedIndets );
  ExtendedkQ:= FreeKAlgebra( ExtendedR, 4, "x" );
  Extendedfam:= FamilyObj( GeneratorsOfAlgebra( ExtendedkQ )[1] );
  Extendedrels:= [ ];
  for r in rels do
    Print( r, "\n" );
    rep:= ExtRepOfObj( r );
    Add( Extendedrels, ObjByExtRep( Extendedfam,  rep ) ) ;
  od;
  return [ ExtendedkQ, Extendedrels ];
end;



ExtendParametrizedAlgebra2:= function( kQ, rels )
  local R, k, indets, ExtendedIndets, t, dt, NewIndets, ExtendedR, ExtendedkQ, kQfam, Extendedfam, Extendedrels, r, rep ;
  R:= LeftActingDomain( kQ );
  k:= LeftActingDomain( R );
  indets:= IndeterminatesOfFunctionField( R );
  ExtendedIndets:= [ ] ;
  for t in indets do
#    dt:= X( k, StringFormatted( "d{}", t ) ) ;
#    Add( ExtendedIndets, dt );
    Add( ExtendedIndets, StringFormatted( "d{}", t ) );
  od;
  ExtendedR:= FunctionField( R, ExtendedIndets );
  ExtendedkQ:= FreeKAlgebra( ExtendedR, 4, "x" );
  Extendedfam:= FamilyObj( GeneratorsOfAlgebra( ExtendedkQ )[1] );
  Extendedrels:= [ ];
  for r in rels do
    rep:= ExtRepOfObj( r );
    Add( Extendedrels, ObjByExtRep( Extendedfam,  rep ) ) ;
  od;
  return [ ExtendedkQ, Extendedrels ];
end;


#################################################################################################################################################

#This section is dedicated to recreating my code for the Bar Complex of an algebra, followed by an attempt at programming in the Gerstenhaber Bracket
#on graded algebras (which may not be finite-dimensional)
#We will start by trying to make it work for finite-dimensional algebras


BarComplexFunctionDimension:= function( f )  #f is a linear map from a tensor power A^{\otimes n}, where n is possibly unknown.
                                    #the function outputs the list [ n, i ]
  local dimAn, dimA, a, b, c ;
  dimAn:= Dimension( Source( f ) ) ;
  dimA:= Dimension( Range( f ) ) ;
  a:= Float( dimAn ) ;
  b:= Float( dimA ) ;
  c:= Log10( a )/Log10( b ) ;
  return Rat( c );
end;



CustomSimpleTensor:= function( TenProd, ElmtList )  #TenProd is a tensor product of vector spaces V_1, ..., V_n, and ElmtList is a list of n vectors, where
                                                    #v_1 = ElmtList[1] in V_1, v_2 = ElmtList[2] in V_2, ..., v_n = Elmt[n] in V_n. The function outputs
                                                    #the simple tensor v_1 (x) v_2 (x) ... (x) v_n
  local TenFam, Rep, s ;
  TenFam:= FamilyObj( Basis( TenProd )[1] );
  Rep:= [ ElmtList, 1 ];
  s:= ObjByExtRep( TenFam, Rep );
  return s ;
end;



SubspacesToTensorProduct:= function( TenProd, SubList ) #TenProd is a tensor product of vector spaces V_1, ..., V_n, and SubList is a list of n subspaces,
                                                        #where A_1 = SubList[1] is a subspace of V_1, ..., and A_n = SubList[n] is a subspace of V_n.
                                                        #The function outputs the space A_1 (x) A_2 (x) ... (x) A_n as a subspace of TenProd.
  local BasisList, A, TensorBasis, iter, B, s, TensorSubspace;
  BasisList:= [ ];
  for A in SubList do
    Add( BasisList, Basis( A ) );
  od;
  TensorBasis:= [ ];
	iter:= IteratorOfCartesianProduct( BasisList );
	for B in iter do
		s:= CustomSimpleTensor( TenProd, B );
		Add( TensorBasis, s );
	od;
	TensorSubspace:= Subspace( TenProd, TensorBasis );
	return TensorSubspace ;
end;



NthTensorPower:= function( A, n )
  local L, i ;
  L:= [ ];
  if n = 0 then
    return LeftActingDomain( A );
  elif n = 1 then
    return A ;
  else
    for i in [1..n] do
      Add( L, A );
    od;
    return TensorProduct( L );
  fi;
end;



NthGradeOfTensorPower:= function( kQ, rels, m, n )  #This function inputs a free algebra kQ, a set of defining relations rels, and two integers
                                                    #m and n, and outputs the nth degree of the mth tensor power of the algebra kQ/rels
                                                    #This function is obsolete, as the space it creates is not considered a subspace of the tensor
                                                    #power by GAP
  local tuples, IndexSet, j, GradeList, i, SummandList, TensorList, triv ;
  if n > 0 then
    tuples:= Tuples( [1..n], m ) ;  #The first step is to create the index set over which we will be taking direct sums, i.e. the set of m-tuples
                                    #[j1, ..., jm] such that j1 + ... + jm = n
    IndexSet:= [ ];
    for j in tuples do
      if Sum(j) = n then
        Add( IndexSet, j );
      fi;
    od;
    GradeList:= [ ];
    for i in [1..n] do
      Add( GradeList, nthGradeOfAlgebraByRels( kQ, rels, i ) );
    od;
    SummandList:= [ ] ;
    for j in IndexSet do
      TensorList:= [ ];
      for i in j do
        Add( TensorList, GradeList[i] );
      od;
      Add( SummandList, TensorProduct( TensorList ) );
    od;
    return Sum( SummandList );
  else
    triv:= nthGradeOfAlgebraByRels( kQ, rels, 0 );
    TensorList:= Tuples( [ triv ], m )[1];
    return TensorProduct( TensorList );
  fi;
end;



GradesOfAlgebraGetter:= function( GradedAlgList, L )  #Inputs a list of graded algebras GradedAlgList and a list of integers L, each integer in L
                                                      #corresponding to a nonzero degree of the algebra in GradedAlgList in the same position. It
                                                      #outputs a list where the ith element is the L[i]th grade of GradedAlgList[i][1].
  local n, i, GradeList ;
  n:= Length( L );
  if Length( GradedAlgList ) = n then
    GradeList:= [ ];
    for i in [1..n] do
      Add( GradeList, GradedPositionFinder( GradedAlgList[i], L[i] ) );
    od;
    return GradeList ;
  else
    Error( "The list of integers L must have the same length as the list of graded algebras" );
  fi;
end;



TensorProductOfGradedAlgebras:= function( GradedAlgs ... )
  local TenProd, AlgList, SumOfDegrees, DegreesOfAlgebras, GradesList, GradedA, m, TensorGrading, DegreeTuples, L, p,
  SubList, TenSubspace, n, i ;
  SumOfDegrees:= [ ];
  AlgList:= [ ];
  DegreesOfAlgebras:= [ ];
#
  for GradedA in GradedAlgs do                          #Creating useful bookkeeping lists for the function
    m:= MinMaxDegreeOfGradedAlgebra( GradedA );
    Add( DegreesOfAlgebras, [ m[1]..m[2] ] );
    Add( AlgList, GradedA[1] );
  od;
#
  TenProd:= TensorProduct( AlgList );
  TensorGrading:= [ ];
  DegreeTuples:= Cartesian( DegreesOfAlgebras );
#
  for L in DegreeTuples do
    if not Sum( L ) in SumOfDegrees then
      Add( SumOfDegrees, Sum( L ) );
      SubList:= GradesOfAlgebraGetter( GradedAlgs, L );
      TenSubspace:= SubspacesToTensorProduct( TenProd, SubList );
      Add( TensorGrading, [ [ TenSubspace ], Sum( L ) ] );
    elif Sum( L ) in SumOfDegrees then
      p:= Position( SumOfDegrees, Sum( L ) );
      SubList:= GradesOfAlgebraGetter( GradedAlgs, L );
      TenSubspace:= SubspacesToTensorProduct( TenProd, SubList );
      Add( TensorGrading[p][1], TenSubspace );
    fi;
  od;
#
  n:= Length( TensorGrading );
  for i in [1..n] do
    TensorGrading[i][1]:= Sum( TensorGrading[i][1] );
  od;
  return [ TenProd, TensorGrading ] ;
end;



ithCircleProduct:= function( f, g, i )
  local n , m, A, An, AnFam, Am, AmFam, k, TenA, BasisTenA, ImageList, b, brep, newb, glist, gelmt, gImage, flist, j, fImage, fg ;
  n:= BarComplexFunctionDimension( f );
  m:= BarComplexFunctionDimension( g );
  A:= Range( f );
  An:= Source( f ); AnFam:= FamilyObj( Basis( An )[1] );
  Am:= Source( g ); AmFam:= FamilyObj( Basis( Am )[1] );
  k:= LeftActingDomain( A );
  TenA:= NthTensorPower( A, n+m-1) ;
  BasisTenA:= Basis( TenA );
  ImageList:= [ ];
  if n = 1 then
    for b in BasisTenA do
      brep:= ExtRepOfObj( b );
      newb:= ObjByExtRep( AmFam, brep );
      gImage:= Image( g, newb );
      fImage:= Image( f, gImage );
      Add( ImageList, fImage );
    od;
    fg:= LeftModuleHomomorphismByImages( TenA, A, BasisTenA, ImageList );
  elif m = 1 then
    for b in BasisTenA do
      brep:= ExtRepOfObj( b );
      gImage:= Image( g, brep[1][i] );
      flist:= [ ];
      flist{[1..(i-1)]}:= brep[1]{[1..(i-1)]} ;
      flist[i]:= gImage ;
      flist{[(i+1)..n]}:= brep[1]{[(i+m)..(n+m-1)]};
      fImage:= Image( f, ObjByExtRep( AnFam, [ flist, One(k) ] ) );
      Add( ImageList, fImage );
    od;
    fg:= LeftModuleHomomorphismByImages( TenA, A, BasisTenA, ImageList );
  else
    for b in BasisTenA do
      brep:= ExtRepOfObj( b );
      glist:= brep[1]{[i..(i+m-1)]};
      gImage:= Image( g, ObjByExtRep( AmFam, [ glist, brep[2] ] ) );
      flist:= [ ];
      flist{[1..(i-1)]}:= brep[1]{[1..(i-1)]} ;
      flist[i]:= gImage ;
      flist{[(i+1)..n]}:= brep[1]{[(i+m)..(n+m-1)]};
      fImage:= Image( f, ObjByExtRep( AnFam, [ flist, One(k) ] ) );
      Add( ImageList, fImage );
    od;
    fg:= LeftModuleHomomorphismByImages( TenA, A, BasisTenA, ImageList );
  fi;
  return fg;
end;



ithCircleProductX:= function( f, n, g, m, i, A, TenA )
  local An, AnFam, Am, AmFam, k, BasisTenA, ImageList, b, brep, newb, glist, gelmt, gImage, flist, j, fImage, fg ;
  An:= Source( f ); AnFam:= FamilyObj( Basis( An )[1] );
  Am:= Source( g ); AmFam:= FamilyObj( Basis( Am )[1] );
  k:= LeftActingDomain( A );
  BasisTenA:= Basis( TenA );
  ImageList:= [ ];
  if n = 1 then
    for b in BasisTenA do
      brep:= ExtRepOfObj( b );
      newb:= ObjByExtRep( AmFam, brep );
      gImage:= Image( g, newb );
      fImage:= Image( f, gImage );
      Add( ImageList, fImage );
    od;
    fg:= LeftModuleHomomorphismByImages( TenA, A, BasisTenA, ImageList );
  elif m = 1 then
    for b in BasisTenA do
      brep:= ExtRepOfObj( b );
      gImage:= Image( g, brep[1][i] );
      flist:= [ ];
      flist{[1..(i-1)]}:= brep[1]{[1..(i-1)]} ;
      flist[i]:= gImage ;
      flist{[(i+1)..n]}:= brep[1]{[(i+m)..(n+m-1)]};
      fImage:= Image( f, ObjByExtRep( AnFam, [ flist, One(k) ] ) );
      Add( ImageList, fImage );
    od;
    fg:= LeftModuleHomomorphismByImages( TenA, A, BasisTenA, ImageList );
  else
    for b in BasisTenA do
      brep:= ExtRepOfObj( b );
      glist:= brep[1]{[i..(i+m-1)]};
      newb:= ObjByExtRep( AmFam, [ glist, brep[2] ] );
      gImage:= Image( g, newb );
      flist:= [ ];
      flist{[1..(i-1)]}:= brep[1]{[1..(i-1)]} ;
      flist[i]:= gImage ;
      flist{[(i+1)..n]}:= brep[1]{[(i+m)..(n+m-1)]};
      fImage:= Image( f, ObjByExtRep( AnFam, [ flist, One(k) ] ) );
      Add( ImageList, fImage );
    od;
    fg:= LeftModuleHomomorphismByImages( TenA, A, BasisTenA, ImageList );
  fi;
  return fg;
end;



CircleProduct:= function( f, g )
  local SummandList, n, m, A, TenA, i, foig, fg ;
  SummandList:= [ ];
  n:= BarComplexFunctionDimension( f );
  m:= BarComplexFunctionDimension( g );
  A:= Range( f );
  TenA:= NthTensorPower( A, n+m-1) ;
  for i in [1..n] do
  foig:= ithCircleProductX( f, n, g, m, i, A, TenA );
    Add( SummandList, (-1)^((i-1)*(m-1))*foig );
  od;
  fg:= Sum( SummandList );
  return fg;
end;



CircleProductX:= function( f, n, g, m, A, TenA )
  local SummandList, i, foig, fg ;
  SummandList:= [ ];
  for i in [1..n] do
  foig:= ithCircleProductX( f, n, g, m, i, A, TenA ); #Print( i, "\n" );
    Add( SummandList, (-1)^((i-1)*(m-1))*foig );
  od;
  fg:= Sum( SummandList );
  return fg;
end;



GerstenhaberBracket:= function( f, g )
  local n, m, A, TenA, fg, gf ;
  n:= BarComplexFunctionDimension( f );
  m:= BarComplexFunctionDimension( g );
  A:= Range( f );
  TenA:= NthTensorPower( A, n+m-1) ;
  fg:= CircleProductX( f, n, g, m, A, TenA );
  gf:= CircleProductX( g, m, f, n, A, TenA );
  return fg - (-1)^((m-1)*(n-1))*gf;
end;



GerstenhaberBracketX:= function( f, n, g, m, A, TenA )
  local fg, gf ;
  fg:= CircleProductX( f, n, g, m, A, TenA ); #Print( "fg\n");
  gf:= CircleProductX( g, m, f, n, A, TenA ); #Print( "gf\n" );
  return fg - (-1)^((m-1)*(n-1))*gf;
end;



MultMap:= function( A )
  local A2, muImageList, b, brep, TenA, mu, df ;
  A2:= NthTensorPower( A, 2 );
  muImageList:= [ ];
  for b in Basis( A2 ) do
    brep:= ExtRepOfObj( b );
    Add( muImageList, brep[2]*brep[1][1]*brep[1][2] );
  od;
  mu:= LeftModuleHomomorphismByImages( A2, A, Basis( A2 ), muImageList );
  return mu;
end;



BarComplexDifferentialImage:= function( f )
  local n, m, A, A2, muImageList, b, brep, TenA, mu, df ;
  n:= BarComplexFunctionDimension( f );
  A:= Range( f );
  A2:= NthTensorPower( A, 2 );
  muImageList:= [ ];
  for b in Basis( A2 ) do
    brep:= ExtRepOfObj( b );
    Add( muImageList, brep[1][1]*brep[1][2] );
  od;
  mu:= LeftModuleHomomorphismByImages( A2, A, Basis( A2 ), muImageList );
  df:= GerstenhaberBracket( f, (-1)*mu );
  return df;
end;



BarComplex:= function( A, n )
  local A2, muImageList, brep, mu, An, TenA, k, H, H1, ImageList, b, d  ;
  A2:= NthTensorPower( A, 2 );
  muImageList:= [ ];
  for b in Basis( A2 ) do
    brep:= ExtRepOfObj( b );
    Add( muImageList, brep[2]*brep[1][1]*brep[1][2] );
  od;
  mu:= LeftModuleHomomorphismByImages( A2, A, Basis( A2 ), muImageList );
  An:= NthTensorPower( A, n );
  TenA:= NthTensorPower( A, n+1 );
  k:= LeftActingDomain( A );
  H:= Hom( k, An, A );
  H1:= Hom( k, TenA, A );
  ImageList:= [ ];
  for b in Basis( H ) do
    Add( ImageList, GerstenhaberBracketX( b, n, -mu, 2, A, TenA ) );
  od;
  d:= LeftModuleHomomorphismByImages( H, H1, Basis( H ), ImageList );
  return d ;
end;
#Will have to change indexing, since bn: Hom(A^{\otimes n-1}, A) -> Hom(A^{\otimes n}, A)

#############################################################################################################################

SubspaceBasisExtender:= function( V, B )  #V is a vector space, and B a linearly independent set of vectors of V
  local ExtendedB, v, W, bV, a, iter ;
  bV:= Basis( V );
  W:= Subspace( V, B, "basis" );
  a:= true ;
  iter:= IteratorByBasis( bV );
  ExtendedB:= ShallowCopy( B );
  for v in iter do
    W:= Subspace( V, ExtendedB );
    if V = W then
      break;
    fi;
    if not v in W then
      Add( ExtendedB, v );
    fi;
  od;
  return ExtendedB;
end;



SectionOfLinearMap:= function( f )
  local V, W, bW, v, ImageList, b, g ;
  V:= Source( f ) ;
  W:= Image( f ) ;
  bW:= Basis( W );
  ImageList:= [ ];
  for b in bW do
    Add( ImageList, PreImagesRepresentative( f, b ) );
  od;
  g:= LeftModuleHomomorphismByImages( W, V, bW, ImageList );
  return g;
end;



#############################################################################################################################

#The following is an attempt to code a function which extends a linear map f: W_2 -> A of degree zero to a linear map
# \tilde{f}: A \otimes A -> A, but specifically we only care about the restriction of \tilde{f} to (A_1 \otimes A_2) \oplus (A_2 \otimes A_1)



OrderedQuadraticBasisOfFreeAlgebra:= function( kQ )
  local gens, n, BasisList, kQ2, i, j, bkQ2 ;
  gens:= NonOneGeneratorsOfAlgebra( kQ );
  n:= Length( gens );
  BasisList:= [ ];
  for i in [1..n] do
    for j in [1..n] do
      Add( BasisList, gens[i]*gens[j] );
    od;
  od;
  kQ2:= nthGradeOfAlgebra( kQ, 2 );
  bkQ2:= Basis( kQ2, BasisList );
  return bkQ2;
end;



QuadraticBasisOfAlgebra:= function( A )
  local B;
  B:= Basis( nthGradeOfAlgebra( A, 2 ) );
  return B;
end;



CubicBasisOfAlgebra:= function( A )
  local B;
  B:= Basis( nthGradeOfAlgebra( A, 3 ) );
  return B;
end;



StructureCoefficients11:= function( A, bA2 )  #This function outputs the structure coefficients of the degree 1 part of A, where the basis is
                                              #taken to be the basis of generators x_1, ..., x_n of A (we assume A is generated in degree 1). It
                                              #outputs a 3D array, where M11[i][j] are the coefficients of x_ix_j with respect to some fixed
                                              #basis bA2 of A.
  local M11, gens, n, i, j ;
  M11:= [ ];
  gens:= NonOneGeneratorsOfAlgebra( A );
  n:= Length( gens );
  for i in [1..n] do
    M11[i]:= [ ];
    for j in [1..n] do
      M11[i][j]:= Coefficients( bA2, gens[i]*gens[j] );
    od;
  od;
  return M11;
end;



StructureCoefficients12:= function( A, bA2, bA3 ) #This function outputs the structure coefficients of the degree 1 part of A, where the basis is
                                                  #taken to be the basis of generators x_1, ..., x_n of A (we assume A is generated in degree 1). It
                                                  #outputs a 3D array, where M11[i][j] are the coefficients of x_ix_j with respect to some fixed
                                                  #basis bA2 of A.
  local M12, gens, n, m, i, j ;
  M12:= [ ];
  gens:= NonOneGeneratorsOfAlgebra( A );
  n:= Length( gens );
  m:= Length( bA2 );
  for i in [1..n] do
    M12[i]:= [ ];
    for j in [1..m] do
      M12[i][j]:= Coefficients( bA3, gens[i]*bA2[j] );
    od;
  od;
  return M12;
end;



StructureCoefficients21:= function( A, bA2, bA3 ) #This function outputs the structure coefficients of the degree 1 part of A, where the basis is
                                                  #taken to be the basis of generators x_1, ..., x_n of A (we assume A is generated in degree 1). It
                                                  #outputs a 3D array, where M11[i][j] are the coefficients of x_ix_j with respect to some fixed
                                                  #basis bA2 of A.
  local M21, gens, n, m, i, j ;
  M21:= [ ];
  gens:= NonOneGeneratorsOfAlgebra( A );
  n:= Length( gens );
  m:= Length( bA2 );
  for i in [1..m] do
    M21[i]:= [ ];
    for j in [1..n] do
      M21[i][j]:= Coefficients( bA3, bA2[i]*gens[j] );
    od;
  od;
  return M21;
end;



RelsToCoefficientMatrix:= function( bA2, rels ) #bA2 is the output of QuadraticBasisOfAlgebra( kQ ), and rels is a set of (quadratic) relations.
                                                #The function outputs the list of relations as column vectors of coefficients w.r.t. bA2
  local n, CoeffMat, Coeff, r ;
  n:= Length( bA2 );
  CoeffMat:= [ ];
  for r in rels do
    Add( CoeffMat, Coefficients( bA2, r ) );
  od;
  return TransposedMat( CoeffMat );
end;



KoszulCochainPartialExtenderCoefficients11:= function( kQ, rels, bkQ2, bA2, f ) #bkQ2 is the output of OrderedQuadraticBasisOfFreeAlgebra( kQ ), and bA2 is
                                                                              #the output of QuadraticBasisOfAlgebra( A ), and rels is a set of (quadratic)
                                                                              #relations. f is a linear map f: W_2 -> A of degree 0, so f: W_2 \to A_2.
                                                                              #Returns a matrix of coefficients that defines a linear extension of f to
                                                                              #\tilde{f}: A_1 \otimes A_1 \to A. Note that A_1 \otimes A_1 \cong kQ_2
  local n, RelsCoeffMat, r, ImageMat, SolMat, p, CoeffMat, i, j, cijk, k;
  n:= Length( NonOneGeneratorsOfAlgebra( kQ ) );
  RelsCoeffMat:= [ ];
  ImageMat:= [ ];
  SolMat:= [ ];
  for r in rels do                                        #We are finding c_{i,j}^k such that if r = \sum_{i,j}r^{i,j}x_ix_j is in rels, then
    Add( RelsCoeffMat, Coefficients( bkQ2, r ) );         #f(r) = \sum_k r_{i,j}\tilde{f}(x_ix_j) = \sum_k \sum_{i,j} c_{i,j}^k r^{i,j}a_k^2 holds
    Add( ImageMat, Coefficients( bA2, Image( f, r ) ) );
  od;
  RelsCoeffMat:= TransposedMat( RelsCoeffMat );
  ImageMat:= TransposedMat( ImageMat );
  for p in ImageMat do
    Add( SolMat, SolutionMat( RelsCoeffMat, p ) );
  od;
  CoeffMat:= [ ];
  for i in [1..n] do                                #We are using the fact that bkQ2 is lexicographically ordered to turn our solution matrix
    CoeffMat[i]:= [ ];                              #into the 3D array as described below. Indeed, (i,j) \mapsto (i-1)*n + j defines an order
    for j in [1..n] do                              #isomorphism \{1, \dots, n\} \times \{1, \dots, n\} \to \{1, \dots, n^2\}, and for bookkeeping
      cijk:= [ ];                                   #purposes we want the (i,j)th entry of CoeffMat to correspond to the ((i-1)*n + j)th column of
      for k in [1..Length(SolMat)] do               #SolMat
        Add( cijk, SolMat[k][(i-1)*n + j] );
      od;
      CoeffMat[i][j]:= cijk ;
    od;
  od;
  return CoeffMat ;
end;

#The matrix generated in the above function a 3D array of coefficients c_{i,j}^k, where $\tilde{f}(x_i \otimes x_j) = \sum_{k} c_{i,k}^k a_k^2,
#where the a_k^2 form a basis for A_2.


SystemToSolveBuilder:= function( kQ, rels, bA2, bA3, M11, M12, M21, f ) #CoeffMat is the output of KoszulCochainPartialExtenderCoefficients( kQ, bkQ2, bA2, rels, f ),
                                                                            #Mij is the output of StructureCoefficientsij
  local bkQ2, CoeffMat, BigMat, n, l, t, m, i, j, k, s;
#  bkQ2:= OrderedQuadraticBasisOfFreeAlgebra( kQ );
#  CoeffMat:= KoszulCochainPartialExtenderCoefficients11( kQ, rels, bkQ2, bA2, f );
  BigMat:= [ ];
  n:= Length( NonOneGeneratorsOfAlgebra( kQ ) );
  l:= Length( bA2 );
  for t in [1..2*n*Length( bA2 )] do
    BigMat[t]:= [ ] ;
    for l in [1..n^3] do
      BigMat[t][l]:= 0;
    od;
  od;
  for m in [1..n^3] do
    i:= ( ( m-1 - ( ( m-1 mod n^2) ) )/n^2) + 1 ;
    j:= ( ( ((m-1) mod n^2) - ((m-1) mod n) )/n ) + 1 ;
    k:= ((m-1) mod n ) + 1 ;
    for s in [1..Length(bA2)] do
      BigMat[(i-1)*n + s][m] := M11[j][k][s] ; #Print( [(i-1)*n + s, m], ", " );
      BigMat[n*Length(bA2) + (s-1)*n + k][m] := -M11[i][j][s]; #Print( [n*Length(bA2) + (s-1)*n + k, m], "\n" );
    od;
  od;
  return BigMat ;
end;



KoszulCochainPartialExtenderCoefficients12and21:= function( kQ, rels, bkQ2, bA2, bA3, M11, M12, M21, f )
  local CoeffMat, BigMat, n, q, m, i, j, k, s, C12C21Matrix, ConstantVector, VariableMatrix, Summands ;
  CoeffMat:= KoszulCochainPartialExtenderCoefficients11( kQ, rels, bkQ2, bA2, f ) ;
  BigMat:= SystemToSolveBuilder( kQ, rels, bA2, bA3, M11, M12, M21, f ) ;
  n:= Length( NonOneGeneratorsOfAlgebra( kQ ) );
  C12C21Matrix:= [ ];
  for q in [1..Length(bA3)] do
    ConstantVector:= [ ];
    for m in [1..n^3] do
      i:= ( ( m-1 - ( ( m-1 mod n^2) ) )/n^2) + 1 ;
      j:= ( ( ((m-1) mod n^2) - ((m-1) mod n) )/n ) + 1 ;
      k:= ((m-1) mod n ) + 1 ;
      Summands:= [ ];
      for s in [1..Length(bA2)] do
        Add( Summands, CoeffMat[i][j][s]*M21[s][k][q] - CoeffMat[j][k][s]*M12[i][s][q] );
      od;
      Add( ConstantVector, Sum( Summands ) );
    od;
    Add( C12C21Matrix, SolutionMat( BigMat, ConstantVector ) );
  od;
  return C12C21Matrix ;
end;



KoszulCochainPartialExtenderCoefficients12and21List:= function( L )
  local C;
  C:= KoszulCochainPartialExtenderCoefficients12and21( L[1], L[2], L[3], L[4], L[5], L[6], L[7], L[8], L[9] );
  return C;
end;



C1221Splitter:= function( C1221 )
  local C12, C21, k, n;
  C12:= [ ];
  C21:= [ ];
  n:= Length( C1221[1] )/2;
  for k in [1..Length(C1221)] do
    C12[k]:= C1221[k]{[1..n]} ;
    C21[k]:= C1221[k]{[(n+1)..(2*n)]} ;
  od;
  return [ C12, C21 ];
end;



AlgebraBExampleGenerator:= function()
  local U, W2, bkQ2, bB2, bB3, B2, Hom2, f, M11, M12, M21 ;
  U:= AlgebraB( 1 );
  W2:= nthKoszulComplexObjectByRels( U[1], U[3], 2 );
  bkQ2:= OrderedQuadraticBasisOfFreeAlgebra( U[2] );
  B2:= nthGradeOfAlgebra( U[1], 2 );
  bB2:= QuadraticBasisOfAlgebra( U[1] );
  bB3:= CubicBasisOfAlgebra( U[1] );
  Hom2:= Hom( GaussianRationals, W2, B2 );
  f:= PseudoRandom( Hom2 );
  M11:= StructureCoefficients11( U[1], bB2 );
  M12:= StructureCoefficients12( U[1], bB2, bB3 );
  M21:= StructureCoefficients21( U[1], bB2, bB3 );
#  return [ U[2], bkQ2, bB2, U[3], f, U[1], bB3 ];
  return [ U[2], U[3], bkQ2, bB2, bB3, M11, M12, M21, f, U[1] ];
end;



AlgebraGExampleGenerator:= function( K, p, f, h )
  local U, W2, bkQ2, bB2, bB3, B2, Hom2, g, M11, M12, M21 ;
  U:= AlgebraG( K, p, f, h );
  W2:= nthKoszulComplexObjectByRels( U[1], U[3], 2 );
  bkQ2:= OrderedQuadraticBasisOfFreeAlgebra( U[2] );
  B2:= nthGradeOfAlgebra( U[1], 2 );
  bB2:= QuadraticBasisOfAlgebra( U[1] );
  bB3:= CubicBasisOfAlgebra( U[1] );
  Hom2:= Hom( K, W2, B2 );
  g:= PseudoRandom( Hom2 );
  M11:= StructureCoefficients11( U[1], bB2 );
  M12:= StructureCoefficients12( U[1], bB2, bB3 );
  M21:= StructureCoefficients21( U[1], bB2, bB3 );
#  return [ U[2], bkQ2, bB2, U[3], f, U[1], bB3 ];
  return [ U[2], U[3], bkQ2, bB2, bB3, M11, M12, M21, g, U[1] ];
end;



AlgebraHExampleGenerator:= function( K, f, h )
  local U, W2, bkQ2, bB2, bB3, B2, Hom2, g, M11, M12, M21 ;
  U:= AlgebraH( K, f, h );
  W2:= nthKoszulComplexObjectByRels( U[1], U[3], 2 );
  bkQ2:= OrderedQuadraticBasisOfFreeAlgebra( U[2] );
  B2:= nthGradeOfAlgebra( U[1], 2 );
  bB2:= QuadraticBasisOfAlgebra( U[1] );
  bB3:= CubicBasisOfAlgebra( U[1] );
  Hom2:= Hom( K, W2, B2 );
  g:= PseudoRandom( Hom2 );
  M11:= StructureCoefficients11( U[1], bB2 );
  M12:= StructureCoefficients12( U[1], bB2, bB3 );
  M21:= StructureCoefficients21( U[1], bB2, bB3 );
#  return [ U[2], bkQ2, bB2, U[3], f, U[1], bB3 ];
  return [ U[2], U[3], bkQ2, bB2, bB3, M11, M12, M21, g, U[1] ];
end;



BracketPrepFunction:= function( A, kQ, rels )
  local bkQ2, bA2, bA3, M11, M12, M21, CoeffMat ;
  bkQ2:= OrderedQuadraticBasisOfFreeAlgebra( kQ ) ;
  bA2:= QuadraticBasisOfAlgebra( A );
  bA3:= CubicBasisOfAlgebra( A );
  M11:= StructureCoefficients11( A, bA2 );
  M12:= StructureCoefficients12( A, bA2, bA3 );
  M21:= StructureCoefficients21( A, bA2, bA3 );
  return [ A, rels, bkQ2, bA2, bA3, M11, M12, M21 ];
end;



IsoTest:= function( m, n )
  local i, j, k ;
  i:= ( ( m-1 - ( ( (m-1) mod n^2) ) )/n^2) + 1 ;
  j:= ( ( ((m-1) mod n^2) - ((m-1) mod n) )/n ) + 1 ;
  k:= ((m-1) mod n ) + 1 ;
  return [ i, j, k ];
end;
