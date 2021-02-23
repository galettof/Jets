jets(ZZ,Ideal):= o -> (n,I) -> (
    --create jet ring
    R:= ring I;
    S:= jets(n,R);
    T:= S[tVar]/ideal(tVar^(n+1));            
    M:= promote(matrix pack(dim R,gens S),T);
    phi:= map(T,R,(basis T)*M);                          
    (m,c):= coefficients(phi gens I,Variables=>{tVar});  
    J:= ideal apply(flatten reverse entries c, f -> lift(f,S));
    
    --conditional to test monomial ideal
    
    if o.Gens then (
	return flatten entries gens J;
	) else (
    	return J;
	);
    )



jetMonomials= (n,f) -> (
    expos:= flatten exponents f;
    jetGens:= pack(n+1, jets(n, ring f, Gens=>true));
    compIndex:= apply(compositions(sum expos,n), lst -> slice(lst,expos));
    combList:= pack(numgens (ring f), 
	pack(2, flatten apply(compIndex, lst -> mingle(lst, jetGens)))
	);
    mons:= apply(combList, lst -> 
	apply(lst , pair-> comb(pair#0, pair#1)
	    )
	);
    apply(mons, product)
    )

--this does not check that I is a monomial ideal
monomialJetsRadical= (n,I) -> (
    R:= jets(n, ring I);
    gensList:= flatten entries gens I;
    jetGens:= unique flatten apply(gensList, gen -> jetMonomials(n,gen));
    squarefreeGens:= apply(apply(jetGens, support),product);
    ideal(jetGens)
    )


indexRing = (d,R) -> (
    --our list of ring symbols to work with
    symList:= apply(gens R, baseName);

    --creates a list of variable names for our index ring
    varNames:=
        for s in symList list (
	    if instance(s,IndexedVariable) then (
	        name= separate("_", toString s);
	        name#0|name#1
            ) else (
	        toString s|"0"
	    )
        );
    
    --create our list of variableses
    varList:=
        for n in varNames list (
       	   if instance(n,Sequence) then (
	       new IndexedVariable from {value n#0,n#1}
	   ) else (
	       value n
	   )
        );
    
    --create our index ring
    indRing:= (coefficientRing R)[
    	mingle for v in varList list (
	    if class v===IndexedVariable then (
	    	apply(d+1, i -> new IndexedVariable from {v#0,(v#1,i)})
	    	) else (
	    	apply(d+1, i -> new IndexedVariable from {v,i})
	    	)
	    )
    	];
    return indRing;
    )
