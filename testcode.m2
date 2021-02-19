restart
load "jetsMethod.m2"
load "helpers.m2"
load "jetsFunctions.m2"


R=QQ[x,y]
f=x*y
g=x^2*y
h=x^3*y 
I= ideal f
J= ideal g
K= ideal h
n=8

S1= jets(1,R);
T1= S1[t];
M1= promote(matrix pack(dim R, gens S1),T1);
phi1= map(T1,R,(basis(0,1,T1))*M1);
(m1,cf1)= coefficients(phi1 gens I,Variables=>{t});
(m1,cg1)= coefficients(phi1 gens J,Variables=>{t});  
(m1,ch1)= coefficients(phi1 gens K,Variables=>{t});  


S2= jets(2,R);
T2= S2[t];
M2= promote(matrix pack(dim R, gens S2),T2);
phi2= map(T2,R,(basis(0,2,T2))*M2);
(m2,cf2)= coefficients(phi2 gens I,Variables=>{t});
(m2,cg2)= coefficients(phi2 gens J,Variables=>{t});
(m2,ch2)= coefficients(phi2 gens K,Variables=>{t});


S3= jets(3,R);
T3= S3[t];
M3= promote(matrix pack(dim R, gens S3),T3);
phi3= map(T3,R,(basis(0,3,T3))*M3);
(m3,cf3)= coefficients(phi3 gens I,Variables=>{t});
(m3,cg3)= coefficients(phi3 gens J,Variables=>{t});
(m3,ch3)= coefficients(phi3 gens K,Variables=>{t});


S= jets(n,R);
T= S[t]/ideal(t^(n+1));
M= promote(matrix pack(dim R, gens S),T);
phi= map(T,R,(basis T)*M);
(m,cf)= coefficients(phi gens I,Variables=>{t});  
J= ideal apply(flatten reverse entries c, f -> lift(f,S))





monomialTest= (n,geners) -> (
--    print("monomial generators:", forLoop);
--    elapsedTime (
--	for gen in geners do(
--	    for i from 0 to n do (
--		jetMonomials(i,gen)  
--		);
--	    );
--    	);
    print("jets original:");
    elapsedTime(
	jets0(n, ideal(geners))
	);
    print("jets method:");
    elapsedTime(
	jets(n,ideal geners)
	);
    )

L= toList(select(10..100, i -> i%10==0))
for i in L do (
    print("order:",i);
    monomialTest(i,(f,g,h));
    )

