load "jetsMethod.m2"
load "jetMaps.m2"

R=QQ[x,y];
I= ideal (x^2+y,x*y);
n=5;
S= jets(n,R);
jets(3,I);

RT=QQ[z_0,z_1]
testMap= map(RT,R,{z_0+z_1^2,z_1-z_0})

m= I.cache.jets#maxOrder;
end


T= S[t]/t^(n+1);
b= basis(0,n,T);
tempS= S;
ringVars= reverse join(
    (for i from 0 to n-1 list( 
    	    gens tempS
    	    ) do (
    	    tempS= coefficientRing tempS)),
    {gens tempS}
    );
M= promote(matrix ringVars,T);
phi= map(T,R,b*M);


--can use the function <degrees> on each of c,u,v,a
(d,c)= coefficients(phi gens I,Monomials=>b_{m+1..n});
u = matrix(entries c);
v= lift(u,S);
a= (map(S,T)) c

jetsProjection= (t,s,R) -> (
    map(jets(t,R),jets(s,R))
    )
--this seems silly.  perhaps check order of source/target and throw error
--if map goes the wrong way?
jetsInclusion= (t,s,R) -> (
    jetsProjection(t,s,R)
    )





