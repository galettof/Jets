load "helpers.m2"



opts:= {};

JetsFrame= new Type of HashTable;

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

jetsRing= (n,J) -> (J.cache#n)

--create jetFrame (container for jet stuff)
    --possibiblity for option of user defined variable names
jets QuotientRing:= o -> R -> (
    varNames:= initJetsVariables ambient R;
    I:= flatten entries presentation R;
    S:= ambient R;
    J0:= coefficientRing S[for n in varNames list (n_0)];
    phi:= map(J0,S,gens J0);
    I0:= apply(I, g -> phi g);
    
    new JetsFrame from {
	cache => new CacheTable from {
	    0=> J0, 
	    maxm=> 0
       	    },
	base=> S,
	jetsGens=> I,
	jetsVariables=> varNames
	}
    )

jets(Ideal,Ring):= o -> (I,R) -> (jets(R/I))    


--catch negative n.  Returning ideal for now.
jets(ZZ,JetsFrame):= o -> (n,J) -> (
    m:= J.cache#maxm;
    bigGens1:= for i from 0 to m list(gens J.cache#i);
    
    
    if m<n then (
        
	--make tower of rings
	varNames:= J.jetsVariables;
    	bigGens2:= 
	    for i from m+1 to n list (
	    	J.cache#i= J.cache#(i-1)[for n in varNames list (n_i)];
	    	gens J.cache#i
		);    

	--get generators
       	S:= J.cache#n;
	I:= J.jetsGens;
	T:= S[t];
	M:= promote(matrix (bigGens1|bigGens2),T);
	phi:= map(T,J.base,basis(0,n,T)*M);
    	(d,c):= coefficients(phi matrix{I},Variables=>{t});
	J.cache#jetsMatrix= matrix reverse entries c;
	J.cache#maxm= n;
	J.cache#varsMatrix= M;
	ideal apply(flatten entries c, f -> lift(f,J.cache#n))
	
    	) else ( 
	ideal apply(flatten entries (J.cache#jetsMatrix^{0..n}),
	    f -> lift(f, J.cache#n))
	
	)
    );
end
