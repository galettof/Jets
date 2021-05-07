opts:= {
    Projective=> false
--    DegreeMap=> null,
--    DegreeLift=> null
    };

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

--generate degree list for jets variables
degGenerator= (n,R) -> (
    for d in degrees R list (
	for l in d list n
	)
    )

--generate degrees/map for truncation ring in ideal calculation
jetsDegrees= opts >> o -> R -> (
    Tdegrees:= null;
    degreeMap:= null;
    
    if o.Projective then (
	Tdegrees= -1* {degree R_0};
	degreeMap= d -> degree 1_R;
	) else (
	Tdegrees= {degree 1_R};
	degreeMap= identity;
	);
    return (Tdegrees, degreeMap);
    )

--------------------------------------------------------------------------
--method functions--------------------------------------------------------
--------------------------------------------------------------------------

jets= method(Options=>opts);

jets(ZZ,Ring):= o -> (n,R) -> (
    --name to assign hashtable stored in basering depending on whether
    --are working in the projective or affine case
    typeName:= if o.Projective then (projets) else (jets);
    jetDegs:= null;
    
    if not R#? typeName then (
	jetDegs= if o.Projective then degGenerator(0, R) else degrees R;
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
    	    jetDegs= if o.Projective then degGenerator(i,R) else degrees R; 
	    S= S[jetsVariables(i,R), 
		Join=> false, 
		Degrees=> jetDegs];
            );
     	R#typeName#maxOrder= n;
	R#typeName#jetsRing= S;
	) else if m>n then (
	for i from 0 to m-n-1 do (
	    S= coefficientRing S;
	    )
	);
    
    S#jets= new CacheTable from {
	jetsBase=> R,
	projective=> o.Projective
	}; 
    return S;
    )

jets(ZZ,Ideal):= o -> (n,I) -> (
    R:= ring I;
    S:= null;--initializes jets ring
    t:= local t;--initializes truncation variable
    typeName:= if o.Projective then (projets) else (jets);
    
    if not I.cache#? typeName then (
	S= jets(0,R, Projective=> o.Projective);
	I.cache#typeName= new CacheTable from {
	    maxOrder=> 0,
	    jetsMatrix=> (map(S,R,vars S)) gens I
	    };
    	);
   
    m:= I.cache#typeName#maxOrder;
    --calculate higher order entries if needed
    if n>m then (
        S= jets(n,R, Projective=> o.Projective);
    	(Tdegrees, degreeMap):= jetsDegrees (R, Projective=> o.Projective);
	T:= S[t, Degrees=> Tdegrees, Join=> false]/(ideal(t^(n+1)));
	tempS:= S;
    	Tpolys:= sum reverse join(
	    (for i from 0 to n-1 list(
		    promote(matrix t^(n-i),T) * vars tempS
		    ) do (
		    tempS= coefficientRing tempS)),
	    {promote (matrix t^0,T) * vars tempS}
	    );
    	phi:= map(T,R, Tpolys,DegreeMap=> degreeMap);
	(d,c):= coefficients(phi gens I);
	resultMatrix:= lift(c,S);
    	
	--update value in ideal cache
	I.cache#typeName#jetsMatrix= resultMatrix;
	I.cache#typeName#maxOrder= n;
	m=n;
	);
   
    --retrieve ideal of appropriate order
    JMatrix:= I.cache#typeName#jetsMatrix; 
    ideal (JMatrix)^{m-n..m}
    )

--how to store ideal information we caculate here?
jets(ZZ,QuotientRing):= o -> (n,R) -> (
    I= ideal R;
    modI= jets(n,I);
    base= ring modI;
    base/modI    
    )

jets(ZZ,RingMap):= o -> (n,phi) -> (
    I:= ideal(phi.matrix);
    typeName:= if o.Projective then (projets) else (jets);
    JR= jets(n,phi.source, Projective=> o.Projective);
    JS= jets(n,phi.target, Projective=> o.Projective);
    targets:= null;
    jets(0,I,Projective=> o.Projective);
    
    if (not phi.cache#? typeName) then (
	phi.cache#typeName= new CacheTable from {
	    maxOrder=> 0,
    	    jetsMap=> map(JS,JR,I.cache#typeName#jetsMatrix)
	    };
	);
    
    m= phi.cache#typeName#maxOrder;
    
    if m < n then (
	jets(n,I, Projective=> o.Projective);
    	targets= (I.cache#typeName#jetsMatrix);	
    	) else (
    	targets= phi.cache#typeName#jetsMatrix^{m-n..m};
	);

    psi:= map(JS,JR,
	flatten transpose targets)
--	DegreeLift=> degreeLift,
--	DegreeMap=> degreeMap);
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
