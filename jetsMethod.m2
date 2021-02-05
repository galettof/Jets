--options list
opts= {
    ReturnVector=>false
    };


jets=method(Options=>opts);

jets(ZZ,Ring):= o -> (n,R) -> (
    --create index ring for jets
    load "indexRing.m2";
    S:= indexRing(n,R);
    return S;
    )

jets(ZZ,Ideal):= o -> (n,I) -> (
    --create jet ring
    S:= jets(n, ring I);
    T:= S[tVar]/ideal(tVar^(n+1));            
    M:= promote(matrix pack(dim R,gens S),T);
    phi:= map(T,R,(basis T)*M);                          
    (m,c):= coefficients(phi gens I,Variables=>{tVar});  
    J:= ideal apply(flatten reverse entries c, f -> lift(f,S));
    
    if o.ReturnVector then( --this is not a vector in the way i was thinking
	result= vector flatten entries gens J;
	) else (
    	result= J;
	);
    return result;
    )

