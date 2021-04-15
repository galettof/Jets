load "jetsMethodProj.m2"
load "homTest.m2"

R0= QQ[x,y,z,Degrees=>{3,3,3}];
S0= QQ[a,b,c];
phi= map(S0,R0,matrix{{a^2*b,b*c^2, c^3}});

R1= QQ[x,y,z,Degrees=>{5,5,6}];
S1= QQ[a,b,c,Degrees=>{2,1,2}];
g0= map(S1,R1,matrix{{a^2*b,b*c^2, c^3}});

R2= QQ[x,y,z]
S2= QQ[a,b,c,Degrees=> {{1,2},{1,2},{1,2}}];
h0= map(S2,R2,matrix{{a^2*b,b*c^2, c^3}});

R3= QQ[x,y,z,Degrees=> {{3,8},{3,6},{3,6}}];
S3= QQ[a,b,c,Degrees=> {{1,3},{1,2},{1,2}}];
k0= map(S3,R3,matrix{{a^2*b,b*c^2, c^3}});


n=2

opts:= {
    Projective=> false,
    DegreeMap=> null,
    DegreeLift=> null
    };

jetsm= opts >> o -> (n,phi) -> (
    I:= ideal(phi.matrix);
    typeName:= if o.Projective then (projets) else (jets);
    
    jets(n,I, Projective=> o.Projective);
    
    (JR, transferR):= flattenRing jets(n,phi.source, Projective=> o.Projective);
    (JS, transferS):= flattenRing jets(n,phi.target, Projective=> o.Projective);
    targs:= transferS (I.cache#typeName#jetsMatrix);
    psi:= map(JS,JR,
	flatten rsort transpose targs^{0..n});
--	DegreeLift=> degreeLift,
--	DegreeMap=> degreeMap);

    (inverse transferS) * psi * transferR
    )


jetsM= opts >> o -> (n,phi) -> (
    I:= ideal(phi.matrix);
    typeName:= if o.Projective then (projets) else (jets);

    jets(n,I, Projective=> o.Projective);
    
    JR= jets(n,phi.source, Projective=> o.Projective);
    JS= jets(n,phi.target, Projective=> o.Projective);
    
    targs:= (I.cache#typeName#jetsMatrix);
    psi:= map(JS,JR,
	flatten rsort transpose targs^{0..n});
--	DegreeLift=> degreeLift,
--	DegreeMap=> degreeMap);
   )

test= (n,phi) -> (
    print("Affine:\t\t" | toString (jetsm(n,phi)===jetsM(n,phi)));
    print("Projective:\t" | toString (jetsm(n,phi,Projective=>true)===jetsM(n,phi,Projective=>true)));
    )

