restart
load "indexRing.m2"
s= 2
R= QQ[x,y,a_0]
f= (x-1)^2 + y + 1
I= ideal f

S= indexRing(s,R)
    
T= S[tVar]/ideal(tVar^(s+1));
M= promote(matrix pack(dim R,gens S),T); --unclear on promote (like lift?)
phi= map(T,R,(basis T)*M);
(m,c)= coefficients(phi gens I,Variables=>{tVar}); --Variables options?
    	    	    	    	    	    	   --What are the lists in c?
ideal apply(flatten reverse entries c, f -> lift(f,S))
    
