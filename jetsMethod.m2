load "helpers.m2"

opts:= {};

jets= method(Options=>opts);

--helpers

--create new-tier variables for jets ring
jetsVariables= (n,R) -> (
    symList:= apply(gens R, baseName);
    nString:= toString n;
    varNames:=
        for s in symList list (
	    if instance(s,IndexedVariable) then (
	        name= separate("_", toString s);
	        name#0|nString|"_"|name#1
            ) else (
	        toString s|nString
	    )
        );
    varNames= apply(varNames,value)
    )




--method functions



jets(ZZ,Ring):= o -> (n,R) -> (
    --the jets ring of order 0..MAYBE jets(Ring) accomplishes this step?
    if not R.? jets then (
	R.jets= new CacheTable from {
	    maxOrder=> 0,
	    jetsRing=> coefficientRing R[jetsVariables(0,R)]
	    }
	);
    
    m:= R.jets#maxOrder;
    S:= R.jets#jetsRing;
    
    --build jet ring tower incrementally up to order n
    if n>m then (
	for i from m+1 to n do(
	    S= S[jetsVariables(i,R)];
            );
     	R.jets#maxOrder= n;
	R.jets#jetsRing= S;
	
	) else if m>n then (
	for i from 0 to m-n-1 do (
	    S= coefficientRing S;
	    )
	); 
    return S;
    )


jets(ZZ,Ideal):= o -> (n,I) -> (
    if not I.cache.? jets then (
	I.cache.jets= new CacheTable from {
	    maxOrder=> 0
	    };
    	);
    
    R:= ring I;
    S:= jets(n,R);
    m:= I.cache.jets#maxOrder;
    
    if n>m then (
	T:= S[t]/t^(n+1);
	tempS:= S;
	ringVars:= (for i from 0 to n-1 list( 
	    gens tempS
	    ) do (
	    tempS= coefficientRing tempS;
	    )) | ({gens tempS});
	M:= promote(matrix reverse ringVars,T);
	phi:= map(T,R,basis(0,n,T)*M);
	(d,c):= coefficients(phi gens I,Variables=>{t});
	I.cache.jets#jetsMatrix= lift(matrix(reverse entries c),S);
	I.cache.jets#maxOrder= n;
	m=n;
	);
   
    JMatrix:= I.cache.jets#jetsMatrix; 
    --flatten? maybe use a matrix?
--    ideal apply(flatten (reverse entries jetsMatrix)_{0..n}, p -> lift(p,S))
--    ideal transpose lift(jetsMatrix^(reverse toList((m-n)..m)),S)
    ideal (JMatrix)^{0..n}
    )
    
end
