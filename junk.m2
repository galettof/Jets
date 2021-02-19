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
