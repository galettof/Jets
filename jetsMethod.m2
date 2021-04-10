-------=-------------------------------------------------------------------
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

--generate ring for special case in projective jets ideals
jetsDegrees:= (n,R) -> (
    --a ring of variables corresponding to unique degrees of variable in R
    baseDegrees:= unique degrees R;
    degreeRing:= jets(n,R,Projective=>true)[for i from 0 to (length baseDegrees-1) list(u_i), 
                       	                    Degrees=>baseDegrees, 
		      	   		    Join=>false];
    
    --a hashtable of these variables and their associated degrees
    degreeHash:= hashTable (for g in gens degreeRing list {degree g, g});    
    
    return (degreeRing, degreeHash);
    )

--------------------------------------------------------------------------
--method functions--------------------------------------------------------
--------------------------------------------------------------------------
opts:= {
    Projective=> false,
    DegreeMap=> null,
    DegreeLift=> null
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
    S:= null;--initializes jets ring
    typeName:= if o.Projective then (projets) else (jets);
    degreeMap:= if o.Projective then (d -> degree 1_R) else identity;
    
    if not I.cache#? typeName then (
	S= jets(0,R, Projective=> o.Projective);
	I.cache#typeName= new CacheTable from {
	    maxOrder=> 0,
	    jetsMatrix=> (map(S,R,vars S,DegreeMap=> degreeMap)) gens I
	    };
    	);
   
    m:= I.cache#typeName#maxOrder;
    
    --calculate higher order entries if needed
    if n>m then (
        S= jets(n,R, Projective=> o.Projective);
	
        --for projective jets of a ring with variables of nonuniform degree
	specCase:= length unique degrees R != 1 and o.Projective;
    	(degreeRing, degreeHash):= if specCase then jetsDegrees(n,R) else (null,null);
	--a ring of degree variables to handle the case of nonuniform degrees 
	--in projective jets 
	U:= S;
	if specCase then (
	    U= degreeRing;
	    varsHash:= hashTable(for v in gens R list ({v, degreeHash#(degree v)}));
	    );
	
   	--substitution ring for jets calculations and a matrix of generators
	T:= U[t, 
	      Degrees=> if (o.Projective and not specCase) then {-1 * degree  R_0} else {degree 1_R}, 
	      Join=> false]/(ideal t^(n+1));
	Tmatrix:= diagonalMatrix(T, for i from 1 to numgens R list(t));    
	
	--if not in the case of nonuniform degrees in 
	--projective jets, this is simply the identity
	Umatrix:= if specCase then (
	    diagonalMatrix(U,values varsHash) 
	    ) else (
	    id_(T^(numgens R))
	    );
	
	--generate jets substitution polynomials
	tempS:= S;
	subMonomials:= reverse join(
	    (for i from 0 to n-1 list( 
		    vars tempS * Tmatrix^(n-i) * Umatrix^i
		    ) do (
		    tempS= coefficientRing tempS)),
	    {vars tempS * Umatrix^n}
	    );
        
	--perform substitution
	phi:= map(T,R,sum subMonomials, DegreeMap=> degreeMap);

        --sort out t variables
    	(d,c):= coefficients(phi gens I, Monomials=> basis T);
        
    	--sort out u variables if necessary
	if specCase then (
	    deHom:= map(U,U, for i from 1 to numgens U list 1_U);
	    c= deHom lift(c,U);
	    );
    
	resultMatrix:= lift(c,S);

	--update value in ideal cache
	I.cache#typeName#jetsMatrix= resultMatrix;
	I.cache#typeName#maxOrder= n;
	);
   
   
    --warning message for special case
    if specCase then (
       stderr << "
       warning: variable degrees nonuniform, possible loss of homogeneity" 
       << endl;
       );    	
   
   
   --retrieve ideal of appropriate order
   JMatrix:= I.cache#typeName#jetsMatrix;
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
