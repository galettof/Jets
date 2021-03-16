load "jetsMethod.m2"

R=QQ[x,y,z];
n=3;
J= ideal (x^2+y, z*y);
I= ideal (x^2*y, z^3);



radicalJets= (n,I) -> (
    if isMonomialIdeal I then (
	baseIdeal:= jets(n,I);
	gensList:= flatten entries gens baseIdeal;
	squarefreeGens:= apply(apply(gensList, support),product);
	ideal(squarefreeGens)
	) else (
	radical jets(n,I)
	)
    )

