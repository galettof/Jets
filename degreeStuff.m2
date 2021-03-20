load "jetsMethod.m2"

Rt=QQ[x,y,z];
IR= ideal(x^2*y, y*z^2);

St=QQ[x,y,z,Degrees=>{2,3,3}];
IS= ideal(x^2*y, y*z^2);

Tt=QQ[x,y,z,Degrees=>{{2,0,0},{2,1,2},{4,3,1}}];
IT= ideal(x^2*y, y*z^2);


R= QQ[x,y,z];
I= ideal(x^2*y, y*z^2);
m=-1;
n=2;


end
    --using homogeneous T basis
        S:= jets(n,R);
	T:= S[u,t,Join=> false]/(ideal(t^(n+1)));--/((ideal(u,t))^(n+1));
	b:= basis (n,T);
	tempS:= S;
	ringVars:= reverse join(
	    (for i from 0 to n-1 list( 
		    gens tempS
		    ) do (
		    tempS= coefficientRing tempS)),
	    {gens tempS}
	    );
	M:= matrix ringVars;
	pM:= b*M;
	phi:= map(T,R,pM, DegreeMap=> L-> {n+1});
	uM:= phi gens I;
	(d,c):= coefficients(uM);
    	result:= lift(c,S);
    	cheat:= matrix(entries result);


--application of ring map p to matrix m from ringmap.m2
--everything in here is homogeneous except the result
debug Core;
--phi':= map(T,R,pM);
--p=phi';
p=phi;
m=gens I;
R := source p;
S1 := target p;
F := p target m;    
E := p source m;

final=map(F,E,
          map(S1,
	      rawRingMapEval(raw p, raw cover F, raw m)), 
          Degree => p.cache.DegreeMap degree m)

step1= rawRingMapEval(raw p, raw cover F, raw m);
step2= map(S1,step1);




    --original
        S:= jets(n,R);
	T:= S[t, Join=> false]/t^(n+1);
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
	
	--generate ringmap
	degreeMap:= for i from 1 to length gens R list (n+1);
	phi:= map(T,R,b*M);
	(d,c):= coefficients(phi gens I,Monomials=>b_{m+1..n});
	result:= lift(c,S);
	
