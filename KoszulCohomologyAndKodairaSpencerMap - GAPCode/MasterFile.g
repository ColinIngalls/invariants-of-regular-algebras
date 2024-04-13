FFF:= function()
  return 1;
end;



path:= FilenameFunc( FFF );
n:= Length( path )-13;
path:= path{[1..n]};


path1:= Concatenation( path, "CodeFiles/Koszul_Cohomology_Calculator/GradingsForKoszulCohomology.g" );
path2:= Concatenation( path, "CodeFiles/Koszul_Cohomology_Calculator/KoszulComplexByRels.g" );
path3:= Concatenation( path, "CodeFiles/Kodaira-Spencer Map/KodairaSpencerMap.g" );
path4:= Concatenation( path, "CodeFiles/Algebras.g" );
path5:= Concatenation( path, "CodeFiles/ParameterizedAlgebras.g" );


Read( path1 );
Read( path2 );
Read( path3 );
Read( path4 );
Read( path5 );

