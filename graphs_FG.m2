--using EdgeIdeals
restart
needsPackage "Jets"
needsPackage "EdgeIdeals"
R=QQ[x,y,z]
G=graph(R,{{x,y},{y,z}})
I=edgeIdeal G
I2=flattenRing(jetsRadical(2,I),Result=>1)
--J2G=graph I2 (works for EdgeIdeals, not for Graphs)
J2G=graph apply(I2_*,support)
--for hypergraphs
H=hyperGraph {x*y*z}
I=edgeIdeal H
I2=flattenRing(jetsRadical(2,I),Result=>1)
J2H=hyperGraph apply(I2_*,support)

--unifying function
restart
--it is necessary to load packages before defining the function
--otherwise jetsRadical, graph, and hyperGraph are defined as symbols
--and don't take on the meaning they have in the packages
needsPackage "Jets"
needsPackage "EdgeIdeals"
jetsGraph = (n,G) -> (
    --get the list of edges of the jets of the (hyper)graph
    E := (flattenRing(jetsRadical(n,edgeIdeal G),Result=>1)) / support;
    --create graph or hypergraph
    if any(E, e -> #e != 2) then (hyperGraph E) else (graph E)
    )
R=QQ[x,y,z,w]
G=graph(R,{{x,y},{y,z}})
J2G=jetsGraph(2,G)
vertexCovers J2G
H=hyperGraph {x*y*z,z*w}
J2H=jetsGraph(2,H)
vertexCovers J2H
--everything appears to work

restart
needsPackage "Jets"
needsPackage "Graphs"
jetsGraph = (n,G) -> (
    --get the list of edges of the jets of the (hyper)graph
    E := (flattenRing(jetsRadical(n,edgeIdeal G),Result=>1)) / support;
    --create graph or hypergraph
    if any(E, e -> #e != 2) then (hyperGraph E) else (graph E)
    )
G=graph {{x,y},{y,z}}
J2G=jetsGraph(2,G)
vertexCovers J2G
needsPackage "Visualize"
openPort "8080"
visualize J2G
closePort()
--everything appears to work
