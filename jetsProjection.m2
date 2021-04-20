load "jetsMethod.m2"

R=QQ[x,y,z];
f=x^2*y;
I= ideal f;
n=2;

RJ= jets(n,R);
IJ= jets(n,I);
fj= (flatten entries gens IJ)_0;

RP= jets(n,R,Projective=> true);
IP= jets(n,I,Projective=> true);
fp= (flatten entries gens IP)_0;





jetsProjection= {Projective=> false} >> o -> (t,s,R) -> (

    if t <= s then error("whoops");    
    (map(jets(t,R,Projective=> o.Projective),jets(s,R,Projective=> o.Projective)))
    ) 

projectJets= method();

projectJets(ZZ,RingElement):= (n,r) -> (
    sourceRing:= ring r;
    isProjective:= sourceRing#jets#projective;
    baseOrder:= (map(ZZ,QQ)) (# gens(sourceRing,CoefficientRing=>ZZ) / numgens sourceRing) - 1;
    
    if not sourceRing#jets#? jetsBase then error("requires jets ring elements");

    R:= sourceRing#jets#jetsBase;
    (jetsProjection(n,baseOrder,R,Projective=> isProjective)) r    
    )

projectJets(ZZ,Matrix):= (n,M) -> (
    sourceRing:= ring M;
    isProjective:= sourceRing#jets#projective;
    baseOrder:= (map(ZZ,QQ)) (# gens(sourceRing,CoefficientRing=>ZZ) / numgens sourceRing) - 1;
    
    if not sourceRing#jets#? jetsBase then error("requires jets ring elements");

    R:= sourceRing#jets#jetsBase;
    (jetsProjection(n,baseOrder,R,Projective=> isProjective)) M
    )

projectJets(ZZ,Ideal):= (n,I) -> (
    ideal projectJets(n,gens I)
    )
