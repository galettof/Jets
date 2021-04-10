load "jetsMethod.m2"
load "homTest.m2"

R0= QQ[x,y,z];
S0= QQ[a,b,c];
f=  map(S0,R0,matrix{{c,a,b}});
f0= map(S0,R0,matrix{{a^2*b,b*c^2, c^3}},DegreeMap=> d -> 3*d);

R1= QQ[x,y,z,Degrees=>{2,3,2}];
S1= QQ[a,b,c,Degrees=>{3,2,2}];
g=  map(S1,R1,matrix{{c,a,b}});
g0= map(S1,R1,matrix{{a^2*b,b*c^2, c^3}},DegreeMap=> d -> 3*d);

R2= QQ[x,y,z,Degrees=> {{1,2},{1,2},{1,2}}];
S2= QQ[a,b,c,Degrees=> {{1,2},{1,2},{1,2}}];
h=  map(S2,R2,matrix{{c,a,b}});
h0= map(S2,R2,matrix{{a^2*b,b*c^2, c^3}},DegreeMap=> d -> 3*d);

R3= QQ[x,y,z,Degrees=> {{1,2},{1,3},{1,2}}];
S3= QQ[a,b,c,Degrees=> {{1,3},{1,2},{1,2}}];
k=  map(S3,R3,matrix{{c,a,b}});
k0= map(S3,R3,matrix{{a^2*b,b*c^2, c^3}},DegreeMap=> d -> 3*d);

n=2

opts:= {
    Projective=> false,
    DegreeMap=> null,
    DegreeLift=> null
    };

jetsm= opts >> o -> (n,phi) -> (
    
I:= ideal(phi.matrix);
    typeName:= if o.Projective then (projets) else (jets);
    degreeMap:= if o.DegreeMap===null then phi.cache.DegreeMap else o.DegreeMap;
    degreeLift:= if o.DegreeLift===null then phi.cache.DegreeLift else o.DegreeLift;
    
    
    jets(n,I, Projective=> o.Projective);
    
    (JR, transferR):= flattenRing jets(n,phi.source, Projective=> o.Projective);
    (JS, transferS):= flattenRing jets(n,phi.target, Projective=> o.Projective);
    targs:= transferS (I.cache#typeName#jetsMatrix);
    psi:= map(JS,JR,
	flatten rsort transpose targs^{0..n},
	DegreeMap=> degreeMap,
	DegreeLift=> degreeLift);
    (inverse transferS) * psi * transferR
    )
