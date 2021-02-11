--BUG: see report

--options list
opts:= {
    Gens=>false
    };


jets= method(Options=>opts);--dependency

jets(ZZ,Ring):= o -> (n,R) -> (
    --create index ring for jets
    load "indexRing.m2";
    S:= indexRing(n,R);
    --this option doesnt work yet
    if o.Gens then (
	return mingle pack(numgens R, gens S);
	) else (
	return S;
	);
    )

jets(ZZ,RingElement):= o -> (n,f) -> (
    load "radicalJets.m2";
    sum jetMonomials(n,f)
    )

jets(ZZ,Ideal):= o -> (n,I) -> (
    --create jet ring
    R:= ring I;
    S:= jets(n,R);
    T:= S[tVar]/ideal(tVar^(n+1));            
    M:= promote(matrix pack(dim R,gens S),T);
    phi:= map(T,R,(basis T)*M);                          
    (m,c):= coefficients(phi gens I,Variables=>{tVar});  
    J:= ideal apply(flatten reverse entries c, f -> lift(f,S));
    
    if o.Gens then (
	return flatten entries gens J;
	) else (
    	return J;
	);
    )

