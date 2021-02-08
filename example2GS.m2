restart
load "jetsMethod.m2"

R=QQ[x]
f= x^3
I= ideal(f)
J= jets(2,I)
--J0= jets(0,I)
--J1= jets(1,I)
--J2= jets(2,I)
--J3= jets(3,I)

gh= (n,f) -> (
    expo= first flatten exponents f;
    J= jets(n,ring f);
    jetGens= gens J;
    comps= compositions(expo,n);
    result= sum apply(comps, lst -> 
	product apply(jetGens, i -> 
	    i^(number(lst, n -> n==(index i))
		)
	    )
	);
    return result;    
    )

gh(2,f)
