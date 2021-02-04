indexRing = (d,R) -> (
    --our list of ring symbols to work with
    symList:= apply(gens R, baseName);

    --creates a list of variable names for our index ring
    varNames=
        for s in symList list (
	    if instance(s,IndexedVariable) then (
	        name= separate("_", toString s);
	        name#0|name#1
            ) else (
	        toString s|"0"
	    )
        );
    
    --create our list of variableses
    varList=
        for n in varNames list (
       	   if instance(n,Sequence) then (
	       new IndexedVariable from {value n#0,n#1}
	   ) else (
	       value n
	   )
        );
    
    --create our index ring
    indRing := (coefficientRing R)[
    	mingle for v in varList list (
	    if class v===IndexedVariable then (
	    	apply(d+1, i -> new IndexedVariable from {v#0,(v#1,i)})
	    	) else (
	    	apply(d+1, i -> new IndexedVariable from {v,i})
	    	)
	    )
    	];
    return indRing;
    )
