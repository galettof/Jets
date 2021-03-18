
---------------------------------------------------------------------------
--helpers------------------------------------------------------------------
---------------------------------------------------------------------------
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


--------------------------------------------------------------------------
--method functions--------------------------------------------------------
--------------------------------------------------------------------------
opts:= {};

jets= method(Options=>opts);


jets(ZZ,Ring):= o -> (n,R) -> (
    --the jets ring of order 0..MAYBE jets(Ring) accomplishes this step?
    if not R.? jets then (
	jetDegs:= degrees R;
	R.jets= new CacheTable from {
	    maxOrder=> 0,
	    jetsRing=> coefficientRing R[jetsVariables(0,R), 
		                         Join=> false,
					 Degrees=> jetDegs],
	    jetsDegrees => jetDegs
	    }
	);
    
    m:= R.jets#maxOrder;
    S:= R.jets#jetsRing;
    
    --build jet ring tower incrementally up to order n
    if n>m then (
	for i from m+1 to n do(
	    S= S[jetsVariables(i,R), 
		 Join=> false,
		 Degrees=> R.jets#jetsDegrees];
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
    R:= ring I;
    if not I.cache.? jets then (
	I.cache.jets= new CacheTable from {
	    maxOrder=> 0,
	    jetsMatrix=> (map((jets(0,R),R,gens jets(0,R)))) gens I
	    };
    	);
    
    m:= I.cache.jets#maxOrder;
    --calculate higher order entries if needed
    if n>m then (
        S:= jets(n,R);
	T:= S[t, Join=> false]/t^(n+1);
	b:= basis T;
	tempS:= S;
	ringVars:= reverse join(
	    (for i from 0 to n-1 list( 
		    gens tempS
		    ) do (
		    tempS= coefficientRing tempS)),
	    {gens tempS}
	    );
	M:= matrix ringVars,T;
	phi:= map(T,R,b*M);
	(d,c):= coefficients(phi gens I,Monomials=>b_{m+1..n});
	resultMatrix:= I.cache.jets#jetsMatrix || lift(c,S);
    	
	--update value in ideal cache
	I.cache.jets#jetsMatrix= resultMatrix;
	I.cache.jets#maxOrder= n;
	);
   
    --retrieve ideal of appropriate order
    JMatrix:= I.cache.jets#jetsMatrix; 
    ideal (JMatrix)^{0..n}
    )

--how to store ideal information we caculate here?
jets(ZZ,RingMap):= o -> (n,phi) -> (
    I:= ideal(phi.matrix);
    jets(n,I);
    
    
    (JR, transferR):= flattenRing jets(n,phi.source);
    (JS, transferS):= flattenRing jets(n,phi.target);
    targs:= transferS (I.cache.jets#jetsMatrix);
    psi:= map(JS,JR,flatten targs^{0..n});
    (inverse transferS) * psi * transferR
    )
    
---------------------------------------------------------------------------
--secondary functions--------------------------------------------------------
---------------------------------------------------------------------------

radicalJets= (n,I) -> (
    if isMonomialIdeal I then (
	baseIdeal:= jets(n,I);
	R:= ring I;
	gensList:= flatten entries gens baseIdeal;
	termList:= apply(gensList, t-> terms(coefficientRing R, t));
	squarefreeGens:= apply(apply(flatten termList, support),product);
	ideal(squarefreeGens)
	) else (
	radical jets(n,I)
	)
    )
