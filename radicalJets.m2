load "jetsMethod.m2"
load "helpers.m2"

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
--    R:= jets(n, ring I);
    gensList:= flatten entries gens I;
    jetGens:= unique flatten apply(gensList, gen -> jetMonomials(n,gen));
    squarefreeGens:= apply(apply(jetGens, support),product)
--    ideal(jetGens)
    )
