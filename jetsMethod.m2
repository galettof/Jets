
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

--generate degree list for projective jets variables
degGenerator= (n,R) -> (
    L:= if isRing R then degrees R else R;
    if n==1 then L else (for a in L list(apply(a, i -> i*n)))
    )

--------------------------------------------------------------------------
--method functions--------------------------------------------------------
--------------------------------------------------------------------------
opts:= {
    Projective=> false
    };

jets= method(Options=>opts);

jets(ZZ,Ring):= o -> (n,R) -> (
    --name to assign hashtable stored in basering depending on whether
    --are working in the projective or affine case
    typeName:= if o.Projective then (projets) else (jets);
    degMultiplier:= null;
    if not R#? typeName then (
	degMultiplier= if o.Projective then 0 else 1;
	jetDegs:= degGenerator(degMultiplier, R);
	R#typeName= new CacheTable from {
	    maxOrder=> 0,
	    jetsRing=> coefficientRing R[jetsVariables(0,R), 
		                         Join=> false,
					 Degrees=> jetDegs],
	    }
	);
    
    m:= R#typeName#maxOrder;
    S:= R#typeName#jetsRing;
    
    --build jet ring tower incrementally up to order n
    --this is inefficient in the affine case
    if n>m then (
	for i from m+1 to n do(
    	    degMultiplier= if o.Projective then i else 1;
	    S= S[jetsVariables(i,R), 
		Join=> false, 
		Degrees=> degGenerator(degMultiplier,R)];
            );
     	R#typeName#maxOrder= n;
	R#typeName#jetsRing= S;
	) else if m>n then (
	for i from 0 to m-n-1 do (
	    S= coefficientRing S;
	    )
	); 
    return S;
    )

jets(ZZ,Ideal):= o -> (n,I) -> (
    R:= ring I;
    S:= null;--S refers to the jets ring
    if not I.cache.? jets then (
	S= jets(0,R);
	I.cache.jets= new CacheTable from {
	    maxOrder=> 0,
	    jetsMatrix=> (map(S,R,vars S)) gens I
	    };
    	);
   
    m:= I.cache.jets#maxOrder;
    --calculate higher order entries if needed
    if n>m then (
        S= jets(n,R);
	T:= S[t, Degrees=> {degree 1_R}, Join=> false]/(ideal(t^(n+1)));
	b:= basis T;
	tempS:= S;
	ringVars:= reverse join(
	    (for i from 0 to n-1 list( 
		    gens tempS
		    ) do (
		    tempS= coefficientRing tempS)),
	    {gens tempS}
	    );
	M:= matrix ringVars;
	phi:= map(T,R,b*M);
	(d,c):= coefficients(phi gens I, Monomials=>b_{m+1..n});
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
