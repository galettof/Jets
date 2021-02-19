restart
load "jetsMethod.m2"
load "helpers.m2"
load "radicalJets.m2"


R=QQ[x,y,z]
f=x^2*y
g=x^2*z

jetMonomials(2,f)
jetMonomials(2,g)
jets(2,f)

I=ideal(f, g)
geners= monomialJetsRadical(2,I)

------
------
------

restart
load "jetsMethod.m2"

R=QQ[x]
f= x^2
I= ideal(f)
J= jets(2,I)
n=2
--J0= jets(0,I)
--J1= jets(1,I)
--J2= jets(2,I)
--J3= jets(3,I)
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

------
------
------


restart
load "jetsMethod.m2"
load "helpers.m2"

R2=QQ[x,y]
f2=x^2*y
I2= ideal(f2)
n2= 2
J= (flatten entries gens jets(n2,I2))#n2


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




    
