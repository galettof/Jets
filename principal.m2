restart
needsPackage "Jets"
principalComponent = method()
principalComponent(ZZ,Ideal) := (n,I) -> (
    R := ring I;
    JR := jets(n,R);
    JI := jets(n,I);
    p := jetsProjection(n,0,R);
    i := map(source p,R,vars source p);
    --compute the singular locus of I
    --map it to the zero jets via the map i
    --then to the n jets via the map p
    sing := p(i(ideal singularLocus I));
    -- need to saturate if I is not radical
    saturate(JI,sing)
    )
--examples
R=QQ[x,y]
I=ideal(y^2-x^3)
JR=jets(2,R)
JI=jets(2,I)
P=primaryDecomposition JI
PC=principalComponent(2,I)
--check
PC==P_1
--
R=QQ[x,y]
I=ideal(x*y*(x+y-1))
JR=jets(2,R)
JI=jets(2,I)
P=primaryDecomposition JI
apply(P,dim)
PC=principalComponent(2,I)
apply(P,c -> c==PC)
