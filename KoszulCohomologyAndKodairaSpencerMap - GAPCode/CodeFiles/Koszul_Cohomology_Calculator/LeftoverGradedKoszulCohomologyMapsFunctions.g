

GradedKoszulCohomologyMapsByRels2:= function( kQ, rels, p, i )
  local K, A, GradedA, GradedWp0, GradedWp, GradedWp1, Wp0, Wp, Wp1, HomWp0i, HomWpi, HomWp1i,
        Dpi, Dp1i ;
  K:= LeftActingDomain( kQ );
  A:= GBQuotient( kQ, rels );
  GradedWp0:= GradednthKoszulComplexObjectByRels( A, rels, p - 1 ); Wp0:= GradedWp0[1];  Print( "Wp0 \n" );
  GradedWp:= GradednthKoszulComplexObjectByRels( A, rels, p ); Wp:= GradedWp[1];  Print( "Wp \n" );
  GradedWp1:= GradednthKoszulComplexObjectByRels( A, rels, p + 1 ); Wp1:= GradedWp1[1]; Print( "Wp1 \n" );
  if p < 0 then
    Error( "Please enter a nonnegative homological degree" );
  elif IsFiniteDimensional( A ) = false and i = "full" then
    Error( "Cannot compute the full cohomology of an infinite-dimensional algebra (yet)");
  elif i = "full" then
    GradedA:= GradingOfAlgebra( A );
    HomWp0i:= Hom( K, Wp0, A );  #HomWp0i:= GradedHomKoszulComplexObjectByRels( GradedA, rels, p-1 )[1] ;
    HomWpi:= Hom( K, Wp, A );  #HomWpi:= GradedHomKoszulComplexObjectByRels( GradedA, rels, p )[1] ;
    HomWp1i:= Hom( K, Wp1, A );  #HomWp1i:= GradedHomKoszulComplexObjectByRels( GradedA, rels, p + 1 )[1] ;
  elif IsInt( i ) = true then
    HomWp0i:= nthGradedHom2( K, GradedWp0, A, i ); Print( "HomWp0i \n" );
    HomWpi:= nthGradedHom2( K, GradedWp, A, i ); Print( "HomWpi \n" );
    HomWp1i:= nthGradedHom2( K, GradedWp1, A, i ); Print( "HomWp1i \n" );
  else
    Error( "Please enter valid inputs" );
  fi;
  if p = 0 then
    Dpi:= TrivialLinearMap( HomWp0i, HomWpi ); Print( "Dpi \n" );
    Dp1i:= HomKoszulDifferential2( A, Wp1, HomWpi, HomWp1i, p+1, i ); Print( "Dpi1 \n" );
  else
    Dpi:= HomKoszulDifferential2( A, Wp, HomWp0i, HomWpi, p, i ); Print( "Dpi \n" );
    Dp1i:= HomKoszulDifferential2( A, Wp1, HomWpi, HomWp1i, p+1, i ); Print( "Dpi1 \n");
  fi;
  return [ Dp1i, Dpi ];
end;


GradedKoszulCohomologyMapsByRels3:= function( kQ, rels, p, i )
  local K, A, GradedA, GradedWp0, GradedWp, GradedWp1, Wp0, Wp, Wp1, HomWp0i, HomWpi, HomWp1i,
        Ai, Dpi, Dp1i ;
  K:= LeftActingDomain( kQ );
  A:= GBQuotient( kQ, rels );
  GradedWp0:= GradednthKoszulComplexObjectByRels( A, rels, p - 1 ); Wp0:= GradedWp0[1];  #Print( "Wp0 \n" );
  GradedWp:= GradednthKoszulComplexObjectByRels( A, rels, p ); Wp:= GradedWp[1];  #Print( "Wp \n" );
  GradedWp1:= GradednthKoszulComplexObjectByRels( A, rels, p + 1 ); Wp1:= GradedWp1[1]; #Print( "Wp1 \n" );
  if p < 0 then
    Error( "Please enter a nonnegative homological degree" );
  elif IsFiniteDimensional( A ) = false and i = "full" then
    Error( "Cannot compute the full cohomology of an infinite-dimensional algebra (yet)");
  elif i = "full" then
    GradedA:= GradingOfAlgebra( A );
    HomWp0i:= Hom( K, Wp0, A );
    HomWpi:= Hom( K, Wp, A );
    HomWp1i:= Hom( K, Wp1, A );
  elif IsInt( i ) = true then
    HomWp0i:= Hom( K, Wp0, nthGradeOfAlgebra( A, i + p-1 ) ) ;
    HomWpi:= Hom( K, Wp, nthGradeOfAlgebra( A, i + p ) ) ;  #This works because of the trivial grading of Wp, for all p
    HomWp1i:= Hom( K, Wp1, nthGradeOfAlgebra( A, i+p+1 ) );
  else
    Error( "Please enter valid inputs" );
  fi;
  if Dimension( HomWpi ) = 0 then   #These are needed to circumvent issues GAP has with the
                                    #Kernel and Image function when the spaces are trivial
    Dpi:= ZeroMapping( HomWp0i, HomWpi ); Print("Cohomology is zero \n");
    Dp1i:= ZeroMapping( HomWpi, HomWp1i );
  elif Dimension( HomWp0i ) = 0 then
    Dpi:= ZeroMapping( HomWp0i, HomWpi ); Print("D^p_i = 0 \n");
    Dp1i:= HomKoszulDifferential2( A, Wp1, HomWpi, HomWp1i, p+1, i );
  elif Dimension( HomWp1i ) = 0 then
    Dpi:= HomKoszulDifferential2( A, Wp, HomWp0i, HomWpi, p, i ); Print("D^{p+1}_i = 0 \n");
    Dp1i:= ZeroMapping( HomWpi, HomWp1i );
  else
    Dpi:= HomKoszulDifferential2( A, Wp, HomWp0i, HomWpi, p, i ); Print( "Dpi != 0 \n" );
    Dp1i:= HomKoszulDifferential2( A, Wp1, HomWpi, HomWp1i, p+1, i ); Print( "Dpi1 != 0 \n");
  fi;
  return [ Dp1i, Dpi ];
end;



####################################################################################################################################################

#The following will serve to define the differentials \tilde{b_K} in the paper Koszul Calculus

TildeHomKoszulDifferentialImage:= function( GradedA, f, Wp, p )  #inputs a linear map f: Wp0 = W_{p-1} -> A and
                                                #outputs the linear map Dpf: W_p ->, A defined in
                                                #the paper Koszul Calculus, after using the
                                                #isomorphism Hom_{A^e}(A(x)Wp(x)A, A) = Hom_k(Wp, A)
  local Dpf, kQ, Wp0, A, ListA, IndexA, Amin, Amax, j, m, Agens, bWp, DpfImageList, x1, x2, xLeftDecomp, xRightDecomp, Summand, i, L ;
  A:= GradedA[1]; ListA:= GradedA[2]; IndexA:= [];
  for x1 in ListA do
    Add( IndexA, x1[2] );
  od;
  Amin:= Minimum( IndexA ); Amax:= Maximum( IndexA );
  for j in [Amin..Amax] do
    if IsSubset( GradedPositionFinder(GradedA, j ), Image( f ) ) = true then
      m:= j ;
    fi;
  od;
  kQ:= Parent( Wp ); bWp:= Basis( Wp );
  Wp0:= Source( f ); #A:= Range( f );
  Agens:= GeneratorsOfAlgebra( A ); Agens:= DuplicateRemover( Agens );
  DpfImageList:= [];
  for x2 in bWp do
    xLeftDecomp:= LeftmostProductDecomposition( kQ, x2 );
    xRightDecomp:= RightmostProductDecomposition( kQ, x2 );
    L:= [];
    for i in [1..Length( Agens )] do
      Summand:= Agens[i]*Image( f, xLeftDecomp[i] ) - (-1)^(m) * Image( f, xRightDecomp[i] )*Agens[i] ;
      Add( L, Summand );
    od;
    Add( DpfImageList, Sum( L ) );
  od;
  Dpf:= LeftModuleHomomorphismByImages( Wp, A, bWp, DpfImageList );
  return Dpf ;
end;


TildeHomKoszulDifferential:= function( GradedA, Wp, GradedHomWp0, GradedHomWp, p ) #outputs Dp: Hom( Wp0, A) -> Hom( Wp, A )
  local Dp, A, K, Wp0, BasisHomWp0, f, ImageList ;
  A:= GradedA[1]; K:= LeftActingDomain( A );
#  Wp0:= nthKoszulComplexObject( A, p-1 ); HomWp0:= Hom( K, Wp0, A );
#  Wp:= nthKoszulComplexObject( A, p ); HomWp:= Hom( K, Wp, A );
  BasisHomWp0:= BasisForGradedAlgebra( GradedHomWp0 ); ImageList:= [];
  for f in BasisHomWp0 do
    Add( ImageList, TildeHomKoszulDifferentialImage( GradedA, f, Wp, p ) );
  od;
  Dp:= LeftModuleHomomorphismByImages( GradedHomWp0[1], GradedHomWp[1], BasisHomWp0, ImageList );
  return Dp ;
end;


TildeGradedKoszulCohomologyMapsByRels:= function( kQ, rels, p, i )
  local A, GradedA, Wp, Wp1, GradedHomWp0, GradedHomWp, GradedHomWp1, HomWp0i, HomWpi, HomWp1i,
        Dpi, Dp1i ;
  A:= GBQuotient( kQ, rels ); GradedA:= GradingOfAlgebra( A );
  Wp:= nthKoszulComplexObjectByRels( A, rels, p );
  Wp1:= nthKoszulComplexObjectByRels( A, rels, p + 1 );
  GradedHomWp0:= GradedHomKoszulComplexObjectByRels( GradedA, rels, p-1 ) ;
  GradedHomWp:= GradedHomKoszulComplexObjectByRels( GradedA, rels, p ) ;
  GradedHomWp1:= GradedHomKoszulComplexObjectByRels( GradedA, rels, p + 1 ) ;
  if i = "full" then
    HomWp0i:= GradedHomWp0 ;
    HomWpi:= GradedHomWp ;
    HomWp1i:= GradedHomWp1 ;
  elif IsInt( i ) = true then
    HomWp0i:= [ GradedPositionFinder( GradedHomWp0, i ), [ [ GradedPositionFinder( GradedHomWp0, i ), 0 ] ] ];
    HomWpi:= [ GradedPositionFinder( GradedHomWp, i ), [ [ GradedPositionFinder( GradedHomWp, i ), 0 ] ] ];
    HomWp1i:= [ GradedPositionFinder( GradedHomWp1, i ), [ [ GradedPositionFinder( GradedHomWp1, i ), 0 ] ] ];
  fi;
  Dpi:= TildeHomKoszulDifferential( GradedA, Wp, HomWp0i, HomWpi, p );
  Dp1i:= TildeHomKoszulDifferential( GradedA, Wp1, HomWpi, HomWp1i, p + 1 );
  return [ Dp1i, Dpi ];
end;
