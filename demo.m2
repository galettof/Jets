--naming conventions for jet variables
restart
needsPackage "Jets"
R=QQ[a,x_1,y_(1,1)]
jets(2,R)
--basic jets functionalities
restart
needsPackage "Jets"
--define a singular curve
R=QQ[x,y]
I=ideal(y^2-x^3)
--compute jets
elapsedTime jets(3,I)
--jets are cached, lower orders too
I.cache.jet.jetsMatrix
elapsedTime jets(3,I)
elapsedTime jets(2,I)
--jets applies to polynomial rings
jets(3,R)
ring jets(3,I) === jets(3,R)
--and quotient rings
Q=R/I
jets(2,Q)
--parametrize the curve
T=QQ[t]
f=map(T,Q,{t^2,t^3})
isWellDefined f
--jets apply to ring mays
j2f=jets(2,f)
--there is a jet projection (algebraically an inclusion)
p32Q=jetsProjection(3,2,Q)
--it is a natural transformation
j3f=jets(3,f)
p32T=jetsProjection(3,2,T)
p32T * j2f === j3f * p32Q
--compute the principal component of the jets
P=principalComponent(2,I)
--it should have the same dimension as the jet scheme
dim P == dim jets(2,I)
--it should be a component of the jet scheme
dec=primaryDecomposition jets(2,I)
any(dec, p -> p == P)
--compute jets of varieties
X=Spec Q
jets(2,X)
jets(2,X) === Spec jets(2,Q)
--jets need not be homogeneous
Proj jets(2,Q)
--use projective grading to get homogeneous ideals
degrees R
jets(2,I)
isHomogeneous oo
degrees jets(0,R,Projective=>true)
degrees jets(1,R,Projective=>true)
degrees jets(2,R,Projective=>true)
jets(2,I,Projective=>true)
isHomogeneous oo
--compute projective jets of varieties
jets(2,X,Projective=>true)
