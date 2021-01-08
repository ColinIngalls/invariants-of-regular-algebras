
ExampleParametrization:= function( k, q )
  local kQ, rels, A ;
  kQ:= FreeKAlgebra( k, 2, "x" );
  rels:= [ kQ.x1*kQ.x2 - q*kQ.x2*kQ.x1 ];
  A:= GBQuotient( kQ, rels );
  return [ A, kQ, rels ];
end;



ParametrizedAlgebraG:= function( K, p, f )
	local PolyRing, t1, t2, PolyQ, rels, G, x1, x2, x3, x4;
  PolyRing:= FunctionField( K, [ "t1", "t2" ] );
  t1:= IndeterminatesOfFunctionField( PolyRing )[1];
  t2:= IndeterminatesOfFunctionField( PolyRing )[2];
	PolyQ:= FreeKAlgebra( PolyRing, 4, "x" );
	rels:= [];
	if f = Zero( kQ ) then
		Error( "f needs to be nonzero" );
	else
		rels[1]:= kQ.x2*kQ.x1 - kQ.x1*kQ.x2 ;
		rels[2]:= kQ.x4*kQ.x3 - p*kQ.x3*kQ.x4 ;
#
		rels[3]:= kQ.x3*kQ.x1 - p*kQ.x1*kQ.x3 ;
		rels[4]:= kQ.x3*kQ.x2 - p*kQ.x1*kQ.x3 - (p*p)*kQ.x2*kQ.x3 - kQ.x1*kQ.x4;
		rels[5]:= kQ.x4*kQ.x1 - p*kQ.x1*kQ.x4 ;
		rels[6]:= kQ.x4*kQ.x2 - f*kQ.x1*kQ.x3 + kQ.x1*kQ.x4 - kQ.x2*kQ.x4;
		G:= GBQuotient( kQ, rels );
		return [G, kQ, rels] ;
	fi;
end;



ParametrizedAlgebraK:= function( K, q ) #q = 1 or q = -1
	local PolyRing, t1, t2, PolyQ, rels, KAlg, x1, x2, x3, x4;
  PolyRing:= FunctionField( K, [ "t1", "t2" ] );
  t1:= IndeterminatesOfFunctionField( PolyRing )[1];
  t2:= IndeterminatesOfFunctionField( PolyRing )[2];
	PolyQ:= FreeKAlgebra( PolyRing, 4, "x" );
	rels:= [];
	rels[1]:= t2*(PolyQ.x2*PolyQ.x1 - q*PolyQ.x1*PolyQ.x2) ;
	rels[2]:= t2*(PolyQ.x4*PolyQ.x3 + PolyQ.x3*PolyQ.x4) ;
#
	rels[3]:= t2*(PolyQ.x3*PolyQ.x1 - PolyQ.x1*PolyQ.x3) ;
	rels[4]:= t2*(PolyQ.x3*PolyQ.x2 - PolyQ.x2*PolyQ.x4) ;
	rels[5]:= t2*(PolyQ.x4*PolyQ.x1 - PolyQ.x1*PolyQ.x4) ;
	rels[6]:= t2*(PolyQ.x4*PolyQ.x2 - t1*PolyQ.x2*PolyQ.x3) ;
	KAlg:= GBQuotient( PolyQ, rels );
	return [ KAlg, PolyQ, rels ];
end;


#################################################################################################################################################################################

AlgebraOverPolynomialsEvaluationByRels:= function( PolyQ, rels, pts ) #Function inputs a free algebra PolyQ over a rational
                                                                      #function field, a set of relations in the algebra and a
                                                                      #list of points in the base field of the function field.
                                                                      #Outputs the algebra PolyQ "evaluated" at the points
  local PolyRing, indets, k, Q, kQ, kQfam, relsEval, r, rEval, relrep, a, coef, coefrep, coefEval ;
  PolyRing:= LeftActingDomain( PolyQ );
  indets:= IndeterminatesOfFunctionField( PolyRing ) ;
  if Length( pts ) = Length( indets ) then
    k:= CoefficientsRing( PolyRing );
    Q:= QuiverOfPathAlgebra( PolyQ );
    kQ:= PathAlgebra( k, Q ); #kQ will have the same generator names as PolyQ
    kQfam:= FamilyObj( GeneratorsOfAlgebra( kQ )[1] );
    relsEval:= [] ;
    for r in rels do
      relrep:= ExtRepOfObj( r )[2];
      rEval:= [] ;
      for a in relrep do
        if IsList(a) then
          Add( rEval, a );
        else
          Add( rEval, Value( a, indets, pts, One( k ) ) ) ;
        fi;
      od;
      rEval:= ObjByExtRep( kQfam, [0, rEval ] ) ;
      Add( relsEval, rEval ) ;
    od;
    return [ kQ, relsEval ] ;
  else
    Error( "You must have as many points as indeterminates" ) ;
  fi;
end;


AlgebraOverPolynomialsEvaluation:= function( PolyQ, elmt, kQ, pts ) #Function inputs a free algebra PolyQ over a rational
                                                                      #function field, a set of relations in the algebra and a
                                                                      #list of points in the base field of the function field.
                                                                      #Outputs the algebra PolyQ "evaluated" at the points
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
    rEval:= ObjByExtRep( kQfam, [ 0, rEval ] ) ;
    return rEval ;
  else
    Error( "You must have as many points as indeterminates" ) ;
  fi;
end;




KS_Action:= function( PolyQ, elmt, pts )  #inputs PolyQ and pts as above, and some element
                                          #elmt of PolyQ. Outputs the element elmt with all
                                          #instances of the indeterminates t_i of the function
                                          #field with t_i - pts[i]

                                          #For now we assume that the coefficients of elmt are
                                          #have a constant polynomial as denominator, and that
                                          #the coefficients are monomials
  local PolyRing, indets, elmtRep, elmtFam, ValueList, i, elmtChanged, coeff, coeffRep, coeffEval, a, PolyRep ;
  PolyRing:= LeftActingDomain( PolyQ );
  indets:= IndeterminatesOfFunctionField( PolyRing );
  if Length( pts ) = Length( indets ) then
    elmtRep:= ExtRepOfObj( elmt )[2] ;
    elmtFam:= FamilyObj( elmt ) ;
    ValueList:= [ ];
    for i in [1..Length( pts )] do
      Add( ValueList, indets[i] - pts[i] );
    od;
    elmtChanged:= [ ] ;
    for a in elmtRep do
      if IsList(a) then
        Add( elmtChanged, a ) ;
      else
        Add( elmtChanged, Value( a, indets, ValueList ) );
      fi;
    od;
    elmtChanged:= ObjByExtRep( elmtFam, [ 0, elmtChanged ] ) ;
    return elmtChanged ;
  else
    Error( "You must have as many points as indeterminates" ) ;
  fi;
end;




KS_Action2:= function( PolyQ, elmt, pts )  #inputs PolyQ and pts as above, and some element
                                          #elmt of PolyQ. Outputs the element elmt with all
                                          #instances of the indeterminates t_i of the function
                                          #field with t_i - pts[i]

                                          #For now we assume that the coefficients of elmt are
                                          #have a constant polynomial as denominator, and that
                                          #the coefficients are monomials
  local PolyRing, indets, elmtRep, elmtFam, ValueList, ZeroList, i, elmtNew, elmtChanged, coeff, coeffRep, coeffEval, a, Val1, Val2 ;
  PolyRing:= LeftActingDomain( PolyQ );
  indets:= IndeterminatesOfFunctionField( PolyRing );
  if Length( pts ) = Length( indets ) then
    elmtRep:= ExtRepOfObj( elmt )[2] ;
    elmtFam:= FamilyObj( elmt ) ;
    ValueList:= [ ];
    ZeroList:= [ ];
    for i in [1..Length( pts )] do
      Add( ValueList, indets[i] - pts[i] );
      Add( ZeroList, Zero( PolyRing ) );
    od;
    elmtChanged:= [ ] ;
    for a in elmtRep do
      if IsList(a) then
        Add( elmtChanged, a ) ;
      elif IsPolynomial(a) then
        Val1:= Value( a, indets, ValueList );
        if IsPolynomial( Val1 ) then
          Val2:= Value( Val1, indets, ZeroList );
          Add( elmtChanged, Val1 - Val2 );
        else
          Add( elmtChanged, a ) ;
        fi;
      else
        Add( elmtChanged, Zero(PolyRing) );
      fi;
    od;
    elmtNew:= ObjByExtRep( elmtFam, [ 0, elmtChanged ] ) ;
    return elmtNew ;
  else
    Error( "You must have as many points as indeterminates" ) ;
  fi;
end;



IndeterminateProductAndConstantKiller:= function( poly )
  local PolyRep, PolyFam, NewPoly, a ;
  PolyRep:= ExtRepPolynomialRatFun( poly );
  PolyFam:= FamilyObj( poly );
  NewPoly:= [ ];
  for a in [1..Length(PolyRep)/2] do
    if Length( PolyRep[2*a-1] ) = 0 or Length( PolyRep[2*a-1] ) > 2 then

    else
      Add( NewPoly, PolyRep[2*a-1] );
      Add( NewPoly, PolyRep[2*a] );
    fi;
  od;
  return PolynomialByExtRep( PolyFam, NewPoly );
end;



KS_Action3:= function( PolyQ, elmt, pts )  #inputs PolyQ and pts as above, and some element
                                          #elmt of PolyQ. Outputs the element elmt with all
                                          #instances of the indeterminates t_i of the function
                                          #field with t_i - pts[i]

                                          #For now we assume that the coefficients of elmt are
                                          #have a constant polynomial as denominator, and that
                                          #the coefficients are monomials

                                          #Not perfect, I need to kill off products ti*tj
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



KSImages:= function( i, PolyQ, PolyRels, kQ, rels, A, KoszulKernel, pts )  #A is the algebra kQ/rels. We assume that the list rels has "the same
                                                                            #order" as PolyRels, i.e. rels[i] is the output of the function
                                                                            #AlgebraOverPolynomialsEvaluation( PolyQ, PolyRels[i], kQ, pts ).
  local PolyRing, indets, k, j, EvalList, FormalPolyRelDerivatives, r1, KStiImages, r2, HomRtoA, RelSubspace, KSti ;
  PolyRing:= LeftActingDomain( PolyQ );
  indets:= IndeterminatesOfFunctionField( PolyRing );
  k:= CoefficientsRing( PolyRing );
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
    Add( KStiImages, AlgebraOverPolynomialsEvaluation(PolyQ, r2, A, pts) );
  od;
  HomRtoA:= Parent( KoszulKernel );
  RelSubspace:= Source( Basis( HomRtoA )[1] );
  KSti:= LeftModuleHomomorphismByImages( RelSubspace, A, rels, KStiImages );
  return KSti ;
end;


#KSImages:= function( PolyQ, PolyRels, kQ, A, pts ) #A is the algebra kQ/rels
#  local GenericTangentSpace, KernelBasis, kQRels, r ;
#  for r in PolyRels do
#    Add( kQRels, AlgebraOverPolynomialsEvaluation( PolyQ, r, kQ, pts ) );
#  od;
#end;
