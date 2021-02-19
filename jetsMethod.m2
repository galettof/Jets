load "helpers.m2"
--BUG: see report

--options list
opts:= {
    Gens=>false
    };

ArcSpace = new Type of HashTable;

jets= method(Options=>opts);

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


jets(ZZ,ArcSpace):= o -> (n,A) -> (    
    m:= max keys A.cache;
    if m==-1 then (
    	
	f := A -> (
	    R:= ring ambient A.base;
	    I:= ideal ring A.base;
	    S:= jets(n,R);
	    T:= S[t];
	    M:= promote(matrix pack(dim R, gens S),T);
	    phi:= map(T,R,(basis(0,n,T)*M));
	    (m,c):= coefficients(phi gens I,Variables=>{t});
	    return (reverse entries c,S,T);
   	    );
	((cacheValue n) f) A;
	
	) else if m < n then (
	--????????????????????
	
	) else if not A.cache#?n then (
        
	h:= A -> (
	    m= max keys A.cache;
	    H= A.cache#m_1;
	    polys= flatten A.cache#m_0_{0..n};
	    S= arcs(n,A); 
	    polys= apply(polys, p -> lift(p,H));
	    forget= map(S, H);
	    polys= apply(polys, p -> forget p);
	    T:= S[t];
	    L:= pack(numgens ambient ring A.base, apply(polys, p-> promote(p,T)));
	    return (L,S,T)
	    );
	((cacheValue n) h) A;
	
	) else (
	print("yay");
	);
    )

arcs= method();
-- for cache:  -1 is null
arcs AffineVariety := X -> (
     new ArcSpace from {
    	cache => new CacheTable from {-1 => null},
	base => X
	}
    )

--gives the index ring of order n in the arc space
arcs (ZZ,ArcSpace) := (n,A) -> (
    m:= max keys A.cache;
    R:= A.cache#m_1;
    C:= coefficientRing R;
    numbase:= numgens ambient ring A.base;
    indexNames:= toSequence apply(take(gens R, numbase), getTable); 

    if n > m then(
	return C[splice flatten {gens R, for i from m+1 to n list(
		    indexNames_0_i,indexNames_1_i)}];
	
	) else if n < m then (
	return C[flatten take(pack(numbase, gens R), n+1)];
	
	) else (
	return R;
	)
    )
