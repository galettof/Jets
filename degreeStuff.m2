load "jetsMethod.m2"

R=QQ[x,y];n
I= ideal (x^2+y,x*y);
n=5;
S= jets(n,R);
jets(3,I);
m= I.cache.jets#maxOrder;

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
phi= map(T,R,basis(0,n,T)*M);


--can use the function <degrees> on each of c,u,v,a
(d,c)= coefficients(phi gens I,Monomials=>b_{m+1..n});
u = matrix(entries c);
v= lift(u,S);
a= (map(S,T)) c







