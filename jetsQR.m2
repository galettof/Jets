load "jetsMethod.m2"

R0=QQ[x,y,z,w];
I0= ideal (x^2);
K=ideal(x^2,y^3);


R=R0/I0;
n=2;

J= ideal y^3;
T=R/J;
V=R0/K;


jetsQ= {Projective=> true} >> o -> (n,R) -> (
    jetGens= presentation R;
    I= jets(n,ideal(jetGens));
    base= ring I;
    base/I	
    )

    


