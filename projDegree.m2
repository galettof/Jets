
load "jetsMethod.m2"
-*
R= QQ[x,y,z];
I= ideal(x^2*y, y*z^2);
*-
degGenerator= (n,R) -> (
    --do we want to accept lists as well?
    L:= if isRing R then degrees R else R;
    if n==1 then L else (for a in L list(apply(a, i -> i*n)))--should we add
    )	     	     	     	     	     	     	     --or mulitply?

opts= {Projective=> false};
jetsp= opts >> o -> (n,R) -> (
    typeName:= if o.Projective then (projets) else (jets);
    degMultiplier:= null;
    if not R.? typeName then (
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
	R#typeName#jetsRing= S
	) else if m>n then (
	for i from 0 to m-n-1 do (
	    S= coefficientRing S;
	    )
	); 
    return S;
    )

