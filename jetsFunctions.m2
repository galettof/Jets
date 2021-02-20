jets0 = (s,I) -> (
    R := ring I;
    symList = apply(gens R,baseName);
    S := (coefficientRing R)[
    	mingle for v in symList list (
	    if class v===IndexedVariable then (
	    	apply(s+1, i ->
		    new IndexedVariable from {v#0,(v#1,i)}
		    )
	    	) else (
	    	apply(s+1, i -> 
		    new IndexedVariable from {v,i}
		    )
	    	)
	    )
    	];
    T := S[tVar]/ideal(tVar^(s+1));
    M := promote(matrix pack(dim R,gens S),T);
    phi := map(T,R,(basis T)*M);
    (m,c) := coefficients(phi gens I,Variables=>{tVar});
    ideal apply(flatten reverse entries c, f -> lift(f,S))
   )

ArcSpace = new Type of HashTable

arcs = method()

arcs AffineVariety := X -> (
    new ArcSpace from {
    	cache => new CacheTable,
	base => X
	}
    )

jets2 = method()

jets2 (ZZ,ArcSpace) := (n,A) -> (
    --temporary function
    f := A -> (
    	X := A.base;
    	I := ideal ring X;
    	J := jets0(n,I);
        Spec ((ring J)/J)
	);
    ((cacheValue n) f) A
    )
