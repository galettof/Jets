load "helpers.m2"
--BUG: see report
--
--options list
opts:= {};

JetsFrame= new Type of HashTable;

jets= method(Options=>opts);

--create names for variables in jetRing (still needs fixed for variables of the
--form a_(i,j,..)
jetCoefficients:= (n,I,R) -> (
    
    )

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

--create jetFrame (container for jet stuff)
jets QuotientRing:= o -> R -> (
    varNames:= initJetsVariables ambient R;
    I:= flatten entries presentation R;
    S:= ambient R;
    J0:= coefficientRing S[for n in varNames list (n_0)];
    phi:= map(J0,S,gens J0);
    I0:= apply(I, g -> phi g);
    
    new JetsFrame from {
	cache=> new CacheTable from {
	    0=> new HashTable from { 
	    	jetsRing=> J0,
	    	jetsGenerators=> I0
      		}
	    },
	base=> S,
	jetsGens=> I,
	jetsVariables=> varNames
	}
    )

jets(Ideal,Ring):= o -> (I,R) -> (jets(R/I))    


--catch negative n.  what, if anything, should this return?
jets(ZZ,JetsFrame):= o -> (n,J) -> (
    m:= max keys J.cache;
    bigGens1:= for i from 0 to m list(gens J.cache#i.jetsRing);
    
    
    if m<n then (
        
	--make tower of rings
	varNames:= J.jetsVariables;
	J.cache#(m+1)= J.cache#m.jetsRing[for n in varNames list(n_(m+1))];
    	bigGens2:= 
	    {gens J.cache#(m+1)} |
	    for i from m+2 to n list (
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
	newGens:= reverse entries c;
        
	--populate jetsFrame
    	f:= (n,J) -> (
	    new HashTable from {
		jetsRing=> J.cache#n,
		jets=> newGens_n
		}
	    );
	for i from m+1 to n do(
	    J.cache#i= f(i,J);
	    print(toString i);
	    );
        --return ideal    
    	) else ( print("wheee")
	--return ideal
	)
    );
end
