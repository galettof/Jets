load "helpers.m2"

opts:= {};

jets= method(Options=>opts);

--helpers

    --issue with variables of the form x_(i,j,..)
initJetsVariables= R -> (
    symList:= apply(gens R, baseName);
    varNames:=
        for s in symList list (
	    if instance(s,IndexedVariable) then (
	        name= separate("_", toString s);
	        name#0|name#1
            ) else (
	        toString s|"0"
	    )
        );
    varNames= apply(varNames,value)
    )

jets(ZZ,Ring):= o -> (n,R) -> (
    --initialize jets base by inserting hashtable into input ring and forming
    --the jets ring of order 0
    if not R.? jets then (
    	varBase:= initJetsVariables ambient R;
	R.jets= new CacheTable from {
	    varis=> varBase,
	    maxOrder=> 0,
	    jetsRing=> coefficientRing R[for name in varBase list (name_0)]
	    }
	);
    
    m:= R.jets#maxOrder;
    varNames:= R.jets#varis;
    S:= R.jets#jetsRing;
    
    --build jet ring tower incrementally up to order n
    if n>m then (
	for i from m+1 to n do(
	    S= S[for name in varNames list(name_i)];
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
    polys:= flatten entries gens I;
    m:= I.cache.jets#maxOrder;
    
    if n>m then (
    	T:= S[t];
	Stemp:= S;
	ringVars:= (for i from 0 to n-1 list( 
	    gens Stemp
	    ) do (
	    Stemp= coefficientRing Stemp;
	    )) | ({gens Stemp});
	M:= promote(matrix reverse ringVars,T);
	phi:= map(T,R,basis(0,n,T)*M);
	(d,c):= coefficients(phi matrix{polys},Variables=>{t});
	I.cache.jets.jetsMatrix= c;
	I.cache.jets#maxOrder= n;
	);
    
    jetsMatrix:= I.cache.jets.jetsMatrix; 
    ideal apply((flatten reverse entries jetsMatrix)_{0..n}, p -> lift(p,S))
    )
    
end

jets (ZZ,RingMap):= o -> (n,phi) -> (
    
    map(JS,R,ph )

    ) 
