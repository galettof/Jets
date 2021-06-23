--exmaple 1
restart
loadPackage "Jets"
R=QQ[x,y,z]
I= ideal(x*y*z)
J2I= jets(2,I)
netList J2I_*
JR2I= jetsRadical(2,I)
netList pack(5,JR2I_*)
P= minimalPrimes J2I
(A,f)= flattenRing ring J2I
needsPackage "LocalRings"
M= cokernel gens f J2I
mult=for p in P list (
    Rp := localRing(A,f p);
    length(M ** Rp)
    );
netList(pack(4,mingle{P,mult}),HorizontalSpace=>1)

--2
restart
loadPackage "Jets"
R=QQ[a..e]
G=graph({{a,c},{a,d},{a,e},{b,c},{b,d},{b,e},{c,e}});
J1G=jets(1,G)
netList pack(7,edges J1G)
J2G= jets(2,G)
netList pack(7,edges J2G)
graphs={G,J1G,J2G}
apply(graphs,chromaticNumber)
apply(graphs, x -> isChordal complementGraph x)
vertexCovers G
netList pack(2,vertexCovers J2G)

--3
restart
loadPackage "Jets"
R=QQ[x_(1,1)..x_(3,3)]
G= genericMatrix(R,3,3)
I1= minors (1,G)
JI1= jets(1,I1)
dim JI1, isPrime JI1
I3= minors(3,G)
JI3= jets(1,I3)
isPrime JI3
I2= minors(2,G)
JI2= jets(1,I2)
P= primaryDecomposition JI2
#P
P_1
radical JI2==JI2
P_0== principalComponent(1,I2,Saturate=>false)
L= apply({P_0,I2}, X -> hilbertSeries(X,Reduce=>true))
numerator first L == (numerator last L)^2
