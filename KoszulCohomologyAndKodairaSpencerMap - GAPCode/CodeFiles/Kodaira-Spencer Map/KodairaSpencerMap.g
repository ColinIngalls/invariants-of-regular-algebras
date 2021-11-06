

#Instructions at the bottom

#ZeroRepRemover:= function( k, elmtrep )
#  local elmtrepcopy, a ;
#  elmtrepcopy:= ShallowCopy( elmtrep );
#  for a in [1..Length(elmtrepcopy)/2] do
#    if elmtrepcopy[2*a] = Zero( k ) then
#      Remove( elmtrepcopy, 2*a-1 );
#      Remove( elmtrepcopy, 2*a-1 );
#    fi;
#  od;
#  return elmtrepcopy ;
#end;



ZeroRepRemover:= function( k, elmtrep )
  local elmtrepcopy, a ;
  elmtrepcopy:= [ ] ;
  for a in [1..Length(elmtrep)/2] do
    if elmtrep[2*a] = Zero( k ) then

    else
      Add( elmtrepcopy, elmtrep[2*a-1] ) ;
      Add( elmtrepcopy, elmtrep[2*a] ) ;
    fi;
  od;
  return elmtrepcopy ;
end;



AlgebraElementOverPolynomialsEvaluation:= function( PolyQ, elmt, kQ, pts )  #Function inputs a free algebra PolyQ over a rational
                                                                            #function field, an element elmt of PolyQ, the free
                                                                            #algebra kQ over the base field, and a list of points
                                                                            #in the base field of the function field over which we
                                                                            #want to evaluate elmt. Outputs the evaluation of elmt at
                                                                            #pts.
  local PolyRing, indets, k, kQfam, relsEval, r, rEval, elmtrep, a, coef, coefrep, coefEval ;
  PolyRing:= LeftActingDomain( PolyQ );
  indets:= IndeterminatesOfFunctionField( PolyRing ) ;
  if Length( pts ) = Length( indets ) then
    kQfam:= FamilyObj( GeneratorsOfAlgebra( kQ )[1] );
    k:= LeftActingDomain( kQ );
#
    elmtrep:= ExtRepOfObj( elmt )[2];
    rEval:= [] ;
    for a in elmtrep do
      if IsList(a) then
        Add( rEval, a );
      else
        Add( rEval, Value( a, indets, pts, One( k ) ) ) ;
      fi;
    od;
    rEval:= ZeroRepRemover( k, rEval );
    rEval:= ObjByExtRep( kQfam, [ 0, rEval ] ) ;
    return rEval ;
  else
    Error( "You must have as many points as indeterminates" ) ;
  fi;
end;



AlgebraEvaluation:= function( PolyQ, PolyRels, pts )  #Function inputs a free algebra PolyQ over a rational
                                                      #function field, a set of relations in the algebra and a
                                                      #list of points in the base field of the function field.
                                                      #Outputs the algebra PolyQ "evaluated" at the points
  local PolyRing, k, Q, kQ, indets, rels, r, A ;
  PolyRing:= LeftActingDomain( PolyQ ); k:= LeftActingDomain( PolyRing );
  indets:= IndeterminatesOfFunctionField( PolyRing );
  if Length( pts ) = Length( indets ) then
    Q:= QuiverOfPathAlgebra( PolyQ );
    kQ:= PathAlgebra( k, Q ); #kQ will have the same generator names as PolyQ, hopefully
    rels:= [];
    for r in PolyRels do
      Add( rels, AlgebraElementOverPolynomialsEvaluation( PolyQ, r, kQ, pts ) );
    od;
    A:= GBQuotient( kQ, rels );
    return [ A, kQ, rels ];
  else
    Error( "You must have as many points as indeterminates" ) ;
  fi;
end;



IndeterminateProductAndConstantKiller:= function( poly )
  local PolyRep, PolyFam, NewPoly, a, b ;
  PolyRep:= ExtRepPolynomialRatFun( poly );
  PolyFam:= FamilyObj( poly );
  NewPoly:= [ ];
  for a in [1..Length(PolyRep)/2] do
#    if Length( PolyRep[2*a-1] ) = 0 or Length( PolyRep[2*a-1] ) > 2 then
#
    if Length( PolyRep[2*a-1] ) = 0 then
      b:= 1;
    elif Length( PolyRep[2*a-1] ) > 2 then
      b:= 1;
    elif PolyRep[2*a-1][2] > 1 then
      b:= 1;
    else
      Add( NewPoly, PolyRep[2*a-1] );
      Add( NewPoly, PolyRep[2*a] );
    fi;
  od;
  return PolynomialByExtRep( PolyFam, NewPoly );
end;




KS_Action3:= function( PolyQ, elmt, pts ) #inputs PolyQ and pts as above, and some element
                                          #elmt of PolyQ. Outputs the element elmt with all
                                          #instances of the indeterminates t_i of the function
                                          #field replaced with t_i + pts[i]

                                          #For now we assume that the coefficients of elmt have
                                          #a constant polynomial as denominator, and that the
                                          #coefficients are monomials
  local PolyRing, indets, elmtRep, elmtFam, ValueList, ZeroList, i, elmtNew, elmtChanged, coeff, coeffRep, coeffEval, a, Val1, Val2 ;
  PolyRing:= LeftActingDomain( PolyQ );
  indets:= IndeterminatesOfFunctionField( PolyRing );
  if Length( pts ) = Length( indets ) then
    elmtRep:= ExtRepOfObj( elmt )[2] ;
    elmtFam:= FamilyObj( elmt ) ;
    ValueList:= [ ];
    ZeroList:= [ ];
    for i in [1..Length( pts )] do
      Add( ValueList, indets[i] + pts[i] );
      Add( ZeroList, Zero( PolyRing ) );
    od;
    elmtChanged:= [ ] ;
    for a in [1..Length(elmtRep)/2] do
      if IsConstantRationalFunction( elmtRep[2*a] ) = false then
        Add( elmtChanged, elmtRep[2*a-1] );
        Val1:= Value( elmtRep[2*a], indets, ValueList );
        if IsPolynomial( Val1 ) then
          Val2:= IndeterminateProductAndConstantKiller( Val1 );
          Add( elmtChanged, Val2 );
#          Val2:= Value( Val1, indets, ZeroList );
#          Add( elmtChanged, Val1 - Val2 );
        else
          Add( elmtChanged, elmtRep[2*a] ) ;
        fi;
#      else
#
      fi;
    od;
    elmtNew:= ObjByExtRep( elmtFam, [ 0, elmtChanged ] ) ;
    return elmtNew ;
  else
    Error( "You must have as many points as indeterminates" ) ;
  fi;
end;



KSImages:= function( i, PolyQ, PolyRels, kQ, rels, KoszulKernel, A, pts ) #We require that kQ and rels are the second and third ouputs of the function
                                                                          #AlgebraEvaluation( PolyQ, PolyRels, pts ). Also, KoszulKernel is the kernel of
                                                                          #GradedKoszulCohomologyMapsByRels( kQ, rels, 2, 0 )[1], and A is the ouput of
                                                                          #GradedKoszulCohomologyMapsByRels( kQ, rels, 2, 0 )[3]

  local PolyRing, indets, k, j, EvalList, FormalPolyRelDerivatives, r1, KStiImages, r2, HomRtoA, RelSubspace, A2, KSti ;
  PolyRing:= LeftActingDomain( PolyQ );
  indets:= IndeterminatesOfFunctionField( PolyRing );
  k:= LeftActingDomain( kQ );
  A2:= nthGradeOfAlgebra( A, 2 );
#  A:= Range( Basis( KoszulKernel )[1] ) ;
  EvalList:= [ ];
  for j in [1..Length(indets)] do
    if j = i then
      Add( EvalList, One(k) ) ;
    else
      Add( EvalList, Zero(k) );
    fi;
  od;
  FormalPolyRelDerivatives:= [ ];
  for r1 in PolyRels do
    Add( FormalPolyRelDerivatives, KS_Action3( PolyQ, r1, pts ) );
  od;
  KStiImages:= [ ];
  for r2 in FormalPolyRelDerivatives do
#    Add( KStiImages, AlgebraElementOverPolynomialsEvaluation( PolyQ, r2, A, pts ) );
    Add( KStiImages, AlgebraElementOverPolynomialsEvaluation( PolyQ, r2, A, EvalList ) );
  od;
#  HomRtoA:= Parent( KoszulKernel );
#  RelSubspace:= Source( Basis( HomRtoA )[1] );
  RelSubspace:= Subspace( kQ, rels );
  KSti:= LeftModuleHomomorphismByImages( RelSubspace, A2, rels, KStiImages );
  return KSti ;
end;



DenominatorOfRelationsKiller:= function( rels )
  local DenomList, r1, r2, RelRep, i, denom, f, rels2 ;
  DenomList:= [];
  for r1 in rels do
    RelRep:= ExtRepOfObj( r1 )[2];
    for i in [1..Length(RelRep)/2] do
      denom:= DenominatorOfRationalFunction( RelRep[2*i] );
      Add( DenomList, denom );
    od;
  od;
  f:= Product( DenomList );
  rels2:= [];
  for r2 in rels do
    Add( rels2, f*r2 );
  od;
  return rels2;
end;



KSMapX:= function( PolyQ, PolyRels, kQ, rels, KoszulKernel, KoszulImage, A, pts )  #pts is a list of points of the field over which the free
                                                                                  #algebra kQ and the polynomial field PolyRing are defined.
                                                                                  #It must have as many elements as PolyRing has indeterminates.
  local PolyRing, indets, k, TanSpace, bTan, NaturalMap, i, ksimage1, ksimage2, KSImageList, KS ;
  PolyRing:= LeftActingDomain( PolyQ );
  indets:= IndeterminatesOfFunctionField( PolyRing );
  k:= LeftActingDomain( kQ );
  if Length( indets ) = Length( pts ) then
    TanSpace:= VectorSpace( k, indets );
    bTan:= Basis( TanSpace );
    NaturalMap:= NaturalHomomorphismBySubspace( KoszulKernel, KoszulImage ) ;
    KSImageList:= [];
    for i in [1..Length( bTan )] do
      ksimage1:= KSImages( i, PolyQ, PolyRels, kQ, rels, KoszulKernel, A, pts );
      ksimage2:= Image( NaturalMap, ksimage1 );
      Add( KSImageList, ksimage2 ) ;
    od;
    KS:= LeftModuleHomomorphismByImages( TanSpace, Image( NaturalMap ), bTan, KSImageList );
    return KS ;
  else
    Error( "You must have as many points as indeterminates" ) ;
  fi;
end;



#Instructions: To use KSmap, you must first define your algebra over a field of rational functions. You do not require the algebra itself,
#but you must have the free algebra PolyQ (an output of FreeKAlgebra) and a set of (quadratic) relations PolyRels. The inputs kQ and rels
#are the objects PolyQ and PolyRels "evaluated" at a list of points pts, where they are evaluated through the function AlgebraEvaluation.
#Then define maps:= GradedKoszulCohomologyMapsByRels:= function( kQ, rels, 2, 0 ), and let KoszulKernel:= Kernel( maps[1] ) (you will have
#to ignore the error and call the function twice), KoszulImage:= maps[2] and A:= maps[3]. Then KSmap will output a linear map from the tangent
#space at pts (here assumed to not be singular, so choose the list pts wisely) into the cohomology group HH^2(A)_0. These steps are steamlined
#into the following three functions.



KSMapSetup1:= function( PolyQ, PolyRels, pts )
  local V, A, maps;
  PolyRels:= DenominatorOfRelationsKiller( PolyRels );
  V:= AlgebraEvaluation( PolyQ, PolyRels, pts );
  maps:= GradedKoszulCohomologyMapsByRels( V[1], V[2], V[3], 2, 0 );;
  return [ PolyQ, PolyRels, V[2], V[3], maps[1], maps[2], maps[3], pts ];
end;



KSMapSetup2:= function( L )
  return [ L[1], L[2], L[3], L[4], Kernel( L[5] ), Image( L[6] ), L[7], L[8] ];
end;



KSMap:= function( L )
  return KSMapX( L[1], L[2], L[3], L[4], L[5], L[6], L[7], L[8] );
end;



#################################################################################################################################################
