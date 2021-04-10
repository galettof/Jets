homTest= f -> (
    if not isHomogeneous f.source then print("source not homogeneous");
    if not isHomogeneous f.target then print("target not homogeneous");
    
    for g in gens(f.source, CoefficientRing=>ZZ) do (
	if not isHomogeneous f g then print(
	    toString g | 
	    " not homogeneous at f"
	    );
	if not (degree f g === f.cache.DegreeMap degree g) then print(
	    "degree of f" | toString g | "=" | toString(degree f g) |
	    " does not match " |
	    "DegreeMap (degree " | toString g | ")=" | toString(f.cache.DegreeMap degree g)
	    );  
	);
    
    if isHomogeneous f then print("good to go!");
    )
     
testIdeal= (n,I) -> (
    IA:= jets(n,I);
    print("Affine Case:");
    print("\tHomogeneous Ideal: " | toString isHomogeneous IA);
    print("\tHomogeneous Matrix: " | toString isHomogeneous I.cache#jets#jetsMatrix);
    
    IP:= jets(n,I,Projective=>true);
    print("Projective Case:");
    print("\tHomogeneous Ideal: " | toString isHomogeneous IA);
    print("\tHomogeneous Matrix: " | toString isHomogeneous I.cache#projets#jetsMatrix);
    )

testMap= (n,f) -> (
    print("Homogeneous Bare Map:\t" | toString isHomogeneous f);
    print("Homogeneous Affine:\t" | toString isHomogeneous jetsm(n,f));
    print("Homogeneous Projective:\t" | toString isHomogeneous jetsm(n,f,Projective=>true));
    )
