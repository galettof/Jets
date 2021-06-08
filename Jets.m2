--------------------------------------------------------------------------------
-- Copyright 2021  Federico Galetto, Nicholas Iammarino
--
-- This program is free software: you can redistribute it and/or modify it under
-- the terms of the GNU General Public License as published by the Free Software
-- Foundation, either version 3 of the License, or (at your option) any later
-- version.
--
-- This program is distributed in the hope that it will be useful, but WITHOUT
-- ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
-- FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
-- details.
--
-- You should have received a copy of the GNU General Public License along with
-- this program.  If not, see <http://www.gnu.org/licenses/>.
--------------------------------------------------------------------------------

newPackage(
     "Jets",
     Version => "0.1",
     Date => "April 22, 2021",
     AuxiliaryFiles => false,
     Authors => {
	 {
	     Name => "Federico Galetto",
	     Email => "galetto.federico@gmail.com",
	     HomePage => "http://math.galetto.org"
	     },
	 {
	     Name=> "Nicholas Iammarino",
	     Email=> "nickiammarino@gmail.com"
	     }
	   },
     Headline => "compute jets of various algebraic, geometric and combinatorial objects",
     PackageImports => {"SimpleDoc","EdgeIdeals"},
     PackageExports => {"EdgeIdeals"},
     DebuggingMode => true
     )



importFrom(MinimalPrimes, {"radical"});
--exportFrom(EdgeIdeals, {"Graph", "HyperGraph"})

-- all user facing symbols, methods, and types must be exported
export {
    "JJ",
    "jets",
    "jetsMaxOrder",
    "jetsBase",
    "jetsRing",
    "projet",
    "jet",
    "jetsMatrix",
    "jetsRadical",
    "jetsProjection",
    "jetsInfo",
    "principalComponent"
    }

jetsOptions= {
    Projective=> false
--    DegreeMap=> null,
--    DegreeLift=> null
    };

---------------------------------------------------------------------------
--helpers------------------------------------------------------------------
---------------------------------------------------------------------------
--create new-tier variables for jets ring
jetsVariables= (n,R) -> (
    symList:= apply(gens R, baseName);
    nString:= toString n;
    varNames:=
        for s in symList list (
	    if instance(s,IndexedVariable) then (
	        name:= separate("_", toString s);
	        name#0|nString|"_"|name#1
            ) else (
	        toString s|nString
	    )
        );
    varNames= apply(varNames,value)
    )

--generate degree list for jets variables
degGenerator= (n,R) -> (
    for d in degrees R list (
	for l in d list n
	)
    )

--generate degrees/map for truncation ring in ideal calculation
jetsDegrees= jetsOptions >> o -> R -> (
    Tdegrees:= null;
    degreeMap:= null;
    
    if o.Projective then (
	Tdegrees= -1* {degree R_0};
	degreeMap= d -> degree 1_R;
	) else (
	Tdegrees= {degree 1_R};
	degreeMap= identity;
	);
    return (Tdegrees, degreeMap);
    )

ambientPoly:= R -> (
    if isPolynomialRing ambient R then (
	return ambient R;
	) else (
	ambientPoly ambient R
	) 
    )

--------------------------------------------------------------------------
--method functions--------------------------------------------------------
--------------------------------------------------------------------------


--Jets (Main Method)------------------------------------------------------

jets= method(Options=>jetsOptions);

jets(ZZ,PolynomialRing):= o -> (n,R) -> (
    if n<0 then error("jets order must be a non-negative integer");
    if not isCommutative R then error("jets method does not support noncommutative rings");
    
    --name to assign hashtable stored in basering depending on whether
    --are working in the projective or affine case
    typeName:= if o.Projective then (projet) else (jet);
    jetDegs:= null;--initialize degree list for jets variables

    if not R#? typeName then (
	jetDegs= if o.Projective then degGenerator(0, R) else degrees R;
	R#typeName= new CacheTable from {
	    (symbol jetsMaxOrder)=> 0,
	    (symbol jetsRing)=> coefficientRing R[jetsVariables(0,R), 
		                                 Join=> false,
					 	 Degrees=> jetDegs],
	    }
	);
    m:= R#typeName#jetsMaxOrder;
    S:= R#typeName#jetsRing;
    
    --build jet ring tower incrementally up to order n
    --this is inefficient in the affine case


    if n>m then (
	for i from m+1 to n do(
    	    jetDegs= if o.Projective then degGenerator(i,R) else degrees R; 
	    S= S[jetsVariables(i,R), 
		Join=> false, 
		Degrees=> jetDegs];
            );
     	R#typeName#jetsMaxOrder= n;
	R#typeName#jetsRing= S;
	) else if m>n then (
	for i from 0 to m-n-1 do (
	    S= coefficientRing S;
	    )
	);
    
    S#jetsInfo= new CacheTable from {
	(symbol jetsBase)=> R,
	(symbol Projective)=> o.Projective
	}; 
    return S;
    )

jets(ZZ,Ideal):= o -> (n,I) -> (
    if n<0 then error("jets order must be a non-negative integer");

    R:= ring I;
    S:= null;--initializes jets ring
    t:= local t;--initializes truncation variable
    
    typeName:= if o.Projective then (projet) else (jet);
    
    if not I.cache#? typeName then (
	S= jets(0,R, Projective=> o.Projective);
	I.cache#typeName= new CacheTable from {
	    (symbol jetsMaxOrder)=> 0,
	    (symbol jetsMatrix)=> (map(S,R,vars S)) gens I
	    };
    	);
   
    m:= I.cache#typeName#jetsMaxOrder;
    
    --calculate higher order entries if needed
    if n>m then (
	S= jets(n,R, Projective=> o.Projective);
    	(Tdegrees, degreeMap):= jetsDegrees (R, Projective=> o.Projective);
	T:= S[t, Degrees=> Tdegrees, Join=> false]/(ideal(t^(n+1)));

	--a row matrix of substitution polynomials in t with coefficients
	--in the jets ring. Calculated incrementally from variables of each
	--level of the tower.
	tempS:= S;
	Tpolys:= sum reverse join(
	    (for i from 0 to n-1 list(
		    promote(matrix t^(n-i),T) * vars tempS
		    ) do (
		    tempS= coefficientRing tempS)),
	    {promote (matrix t^0,T) * vars tempS}
	    );
	
    	phi:= map(T,R,Tpolys,DegreeMap=> degreeMap);

	--a list of generators for I is obtained to avoid dropping/repeating
	geners:= for i from 0 to (numgens I)-1 list I_i;
    	--condition determining if all generators of the ideal are constants
	constCond:= all(geners,isConstant);
    	--add dummy generator to avoid loss of zeros
	gensI:= if constCond then matrix{geners|{R_0}} else matrix{geners};
    	(d,c):= coefficients(phi gensI);
    	--remove dummy generators if necessary
	if constCond then (
		L:= entries c;
		c= matrix (for l in L list drop(l,-1));
		);

	resultMatrix:= lift(c,S);

	--update value in ideal cache
	I.cache#typeName#jetsMatrix= resultMatrix;
	I.cache#typeName#jetsMaxOrder= n;
	m=n;
	);
   
    --retrieve ideal of appropriate order
    JMatrix:= I.cache#typeName#jetsMatrix; 
    if zero JMatrix then return ideal(0_(jets(n,R)));
    f:= map(jets(n,R,Projective=> o.Projective),jets(m,R, Projective=> o.Projective));
    J:= f ideal (JMatrix^{m-n..m});

    J.cache#jetsInfo= new CacheTable from {
	jetsBase=> I,
	Projective=> o.Projective
	};
    
    return J;
    )

jets(ZZ,QuotientRing):= o -> (n,R) -> (
    splitQuotient:= presentation R;
    ambientRing:= ring splitQuotient;
--    ambientRing:= ambientPoly R;
    base:= null; --jets ring to be used in quotient
    modI:= null; --jets ideal to be used in quotient
    Q:= null; --variable to store quotient ring
    
    typeName:= if o.Projective then (projet) else (jet);
    if not R#? typeName then (
	base= jets(0, ambientRing, Projective=> o.Projective);
	modI= jets(0, ideal(splitQuotient), Projective=> o.Projective);
	R#typeName= new CacheTable from {
	    (symbol jetsRing)=> new CacheTable from {
		0 => base/modI
		},
	    };
	);
    
    --form the jets of a quotient ring by taking the quotients of a jets
    --ring and a jets ideal.  Each order of the quotient is stored in a
    --cache table with the integer value of the order as the key    
    if R#typeName#jetsRing#? n then (
	Q= R#typeName#jetsRing#n;
	) else (
	base= jets(n, ambientRing, Projective=> o.Projective);
	modI= jets(n, ideal(splitQuotient), Projective=> o.Projective);
	Q= base/modI;
	R#typeName#jetsRing#n= Q;
	Q#jetsInfo= new CacheTable from {
    	    jetsBase=> R,
       	    Projective=> o.Projective
	    }
	);
    
    return Q;
    )


jets(ZZ,RingMap):= o -> (n,phi) -> (
    I:= ideal(phi.matrix);
    typeName:= if o.Projective then (projet) else (jet);
    if n<0 then error("jets order must be a non-negative integer");
    
    -- check whether jets have previously been calculated for this map
    if (not phi.cache#? typeName) then (
	jets(0,I, Projective=> o.Projective);
	phi.cache#typeName= new CacheTable from {
	    (symbol jetsMaxOrder)=> 0,
    	    (symbol jetsMatrix)=> (map(jets(0,phi.target, Projective=> o.Projective),
		    	    	       jets(0,phi.source, Projective=> o.Projective),
		                       I.cache#typeName#jetsMatrix)).matrix
	    };
	);

    JR:= jets(n,phi.source, Projective=> o.Projective);
    JS:= jets(n,phi.target, Projective=> o.Projective);
    targets:= null;
    
    --check whether lower order jets have already been calculated
    m:= phi.cache#typeName#jetsMaxOrder;
    if m < n then (
	jets(n,I, Projective=> o.Projective);
    	targets= (I.cache#typeName#jetsMatrix);	
	phi.cache#typeName#jetsMaxOrder= n;
	phi.cache#typeName#jetsMatrix= targets;
    	) else (
    	targets= phi.cache#typeName#jetsMatrix^{m-n..m};
	);

    psi:= map(JS,JR,
	flatten transpose targets);
--	DegreeLift=> degreeLift,
--	DegreeMap=> degreeMap);
    
    psi.cache#jetsInfo= new CacheTable from {
    	jetsBase=> phi,
    	Projective=> o.Projective
    	};	  
    
    return psi;
   )

jets(ZZ,Graph):= o -> (n,G) -> (
    --get the list of edges of the jets of the (hyper)graph
    --ring is flattened because graphs don't play well with towers of rings
    E := (flattenRing(jetsRadical(n,edgeIdeal G),Result=>1)) / support;
    --create graph
    graph E
    )

jets(ZZ,HyperGraph):= o -> (n,G) -> (
    --get the list of edges of the jets of the (hyper)graph
    --ring is flattened because graphs don't play well with towers of rings
    E := (flattenRing(jetsRadical(n,edgeIdeal G),Result=>1)) / support;
    --create hypergraph
    hyperGraph E
    )

---Secondary Methods--------------------------------------------------

--to reduce computation time for monomial jet ideals  (cite article of 
--Goward and Smith)
jetsRadical= method(); 

jetsRadical(ZZ,Ideal):= (n,I) -> (

    if n<0 then error("jets order must be a non-negative integer");
    
    if isMonomialIdeal I then (
	baseIdeal:= jets(n,I);
	R:= ring I;
	gensList:= flatten entries gens baseIdeal;
	termList:= apply(gensList, t-> terms(coefficientRing R, t));
	squarefreeGens:= apply(apply(flatten termList, support),product);
	ideal(squarefreeGens)
	) else (
	radical jets(n,I)
	)
    )


--to create a map sending elements of a jets ring to a jets ring of
--higher order
jetsProjection= method(Options=>jetsOptions);

jetsProjection(ZZ,ZZ,PolynomialRing):=
jetsProjection(ZZ,ZZ,QuotientRing):= o -> (t,s,R) -> (

    if t < s then error("first argument must be less than or equal to the second");    
    if t<0 or s<0 then error("jets orders must be non-negative integers");

    (map(jets(t,R,Projective=> o.Projective),jets(s,R,Projective=> o.Projective)))
    ) 

JJ = new ScriptedFunctor from {
     subscript => (
	  i -> new ScriptedFunctor from {
	       argument => (X -> (
	       	    	 jetsOptions >> o -> Y -> (
		    	      f := lookup(jets,class i,class Y);
		    	      if f === null then error "no method available"
		    	      else (f o)(i,Y)
			      )
	       	    	 ) X
	       	    )
	       }
	  )
     }
 
--compute an ideal whose vanishing locus is the
--principal component of the jets of an ideal
principalComponent = method()
principalComponent(ZZ,Ideal) := (n,I) -> (
    -- compute jets of I
    JI := jets(n,I);
    -- get the jets projection
    R := ring I;
    p := jetsProjection(n,0,R);
    -- identify original ambient ring with 0-jets
    i := map(source p,R,vars source p);
    --compute the singular locus of I
    --map it to the zero jets via the map i
    --then to the n jets via the map p
    sing := p(i(ideal singularLocus I));
    -- need to saturate because JI need not be radical
    saturate(JI,sing)
    )

beginDocumentation()
----------------------------------------------------------------------
-- TESTS
----------------------------------------------------------------------
TEST ///
    R= QQ[x,y,z];
    assert(degrees jets(2,R)==={{1}, {1}, {1}})
    assert(degrees jets(2,R,Projective=> true) === {{2}, {2}, {2}})
    I=ideal(y-x^2,z-x^3);
    assert(not(isHomogeneous jets(2,I)))
    assert(isHomogeneous jets(2,I,Projective=>true))
///

--for non uniform degrees
TEST ///
    R= QQ[x,y,z, Degrees=> {2,3,1}];
    assert(degrees jets(2,R)==={{2}, {3}, {1}})
    assert(degrees jets(2,R,Projective=> true) === {{2}, {2}, {2}})
    I= ideal(x*y, x*z^2);
    J= ideal(x^3-y*z^3, y+x*z);
    assert(isHomogeneous jets(2,I))
    assert(isHomogeneous jets(2,I,Projective=>true))
    assert(isHomogeneous jets(2,J))
    assert(isHomogeneous jets(2,J,Projective=>true))
    X= radical jets(2,I);
    Y= jetsRadical(2,I);
    assert(X == Y)
    assert(mingens X === mingens Y);
///

TEST ///
    R=QQ[x,y, Degrees=> {2,3}];
    S=QQ[a,b,c, Degrees=> {1,1,2}]
    phi= map(S,R, {a^2 + c, b*c});
    f= jets(2,phi);
    testx= c2+2*a0*a2+a1^2;
    testy= b0*c2+c0*b2+b1*c1;
    assert(f x2===testx)
    assert(f y2===testy)
    assert(isHomogeneous jets(3,phi))
    assert(isHomogeneous jets(3,phi,Projective=>true))
///

--for ideals with constant generators
TEST ///
    R=QQ[x]
    I0= ideal(2_R)
    Ftest0=jets(2,I0)
    assert(Ftest0==jets(2,R))
    I1= ideal(2_R,x)
    Ftest1=jets(2,I1)
    assert(Ftest1== jets(2,R))
    S=ZZ[x]
    J0= ideal(2_S)
    Ztest0= jets(2,J0)
    assert(Ztest0!=jets(2,S))
    J1= ideal(2_S,x) 
    Ztest1=jets(2,J1)
    assert(Ztest1!=jets(2,S))
///

--for principal component
TEST ///
    R=QQ[x,y]
    I=ideal(y^2-x^3)
    PC=principalComponent(2,I)
    P=primaryDecomposition jets(2,I)
    C=first select(P,c -> degree c==6)
    assert(PC==C)
///


----------------------------------------------------------------------
-- Documentation
----------------------------------------------------------------------
doc ///

Node
    Key
    	Jets
    Headline
    	compute jets of various algebraic, geometric and combinatorial objects
    Description
    	Text
	    This package enables computations with jet functors.
	    It introduces the @TO jets@ method to compute jets of
	    polynomial rings, ideals, quotients, ring homomorphisms,
	    and varieties.
	    
	    The construction of jets follows an algebraic procedure
	    discussed in several sources, including the first three
	    references below.
	    
	    Additional features include an alternative algorithm to compute
	    the radical of jets of monomial ideals, a function
	    to construct jets of graphs, and an option for jets with
	    "projective" gradings.
    References
    	@arXiv("math/0612862","L. Ein and M. Mustaţă,
    		Jet schemes and singularities.")@
		
    	@arXiv("2104.08933","F. Galetto, E. Helmick, and M. Walsh,
    		Jet graphs.")@
		
    	@HREF("https://doi.org/10.1080/00927870500454927",
	    "R.A. Goward and K.E. Smith,
	    The jet scheme of a monomial scheme.")@

    	@arXiv("math/0407113","P. Vojta,
	    	Jets via Hasse-Schmidt Derivations.")@
    Subnodes
    	jets
	jetsProjection
	jetsRadical
	[jets,Projective]
	principalComponent
	"Storing Computations"
	"Examples of functionality"

Node
    Key
    	jets
    Headline
    	compute the jets of an object
    Subnodes	
	(jets,ZZ,PolynomialRing)
	(jets,ZZ,Ideal)
	(jets,ZZ,QuotientRing)
	(jets,ZZ,RingMap)
	(jets,ZZ,Graph)
	JJ
	
Node
    Key
    	"Storing Computations"
    Description
    	Text
	    After the jets of an object are computed, some elements are 
	    stored in a @TO CacheTable@ which, in turn, is stored in the 
	    base object.  Note: no information on the jets of a graph is 
	    stored in its base.
    	Example
	    R= QQ[x,y]
	    I= ideal (x^2 - y)
	    jets(3,I)
	    keys I.cache.jet
    Subnodes
	jet

	projet
	jetsRing
	jetsMaxOrder
	jetsMatrix
	jetsBase
    	jetsInfo    


Node
    Key
	(jets,ZZ,PolynomialRing)
    Headline
    	compute jets of a polynomial ring
    Usage
    	jets (n,R)
    Inputs
    	n:ZZ
    	R:PolynomialRing
    Outputs
    	:PolynomialRing
       	 of jets order @TT "n"@.
    Description
    	Text
	    This function is provided by the package @TO Jets@.  Rings are 
	    constructed incrementally as towers.  The function returns the 
	    ring with variables in the jets order requested, and coeffients 
	    in all lower orders.  The grading or multigrading of the jets ring 
	    follows from that of the base ring.
    	Example	    
	    R= QQ[x,y,z,Degrees=>{2,1,3}]
	    JR= jets(2,R)
	    describe JR
    	    degrees (flattenRing JR)_0	    
    	Text
	    When the @TO [jets,Projective]@ option is set to true, the degree 
	    of each jets variable matches the jets order, in accordance with
	    Proposition 6.6 (c) of @arXiv("math/0407113","P. Vojta,
	    	Jets via Hasse-Schmidt Derivations")@.
    	Example
	    R=QQ[x,y,z,Degrees=>{2,1,3}]
	    JR= jets(2,R,Projective=>true)
	    degrees (flattenRing JR)_0
    	Text
	    The convention for labeling variables in the jets of polynomial ring
	    is to append the order of the jets to name of the variables in the
	    base ring. Existing subscripts are preserved.
    	Example
	    A=QQ[a_1..a_3]
	    JA= jets(1,A)
	    describe JA
    	Text
	    Note that the coefficient ring of the polynomial ring does not need
	    to be a field. The jets of the input polynomial ring will be a
	    polynomial ring with the same coefficient ring as the input.
    	Example
	    Zi=ZZ[i]/ideal(i^2+1)
	    B=Zi[b_1..b_3]
	    JB= jets(1,B)
	    describe JB
	    	  
Node
    Key
	(jets,ZZ,Ideal)
    Headline
    	compute jets of a an ideal in a polynomial ring
    Usage
    	jets (n,I)
    Inputs
    	n:ZZ
	I:Ideal
    Outputs
        :Ideal
	 generated by the jets of the generators of @TT "I"@
    Description
    	Text
	    This function is provided by the package
	    @TO Jets@.
    	Example	    
	    R= QQ[x,y]
	    I= ideal (x^3 + y^3 - 3*x*y)
    	    J= jets(3,I);
	    netList J_*
	Text
	    When the @TO [jets,Projective]@ option is set to true, the degree
	    of each jets variable matches its order, in accordance with
	    Proposition 6.6 (c) of @arXiv("math/0407113","P. Vojta,
	    	Jets via Hasse-Schmidt Derivations")@.
	    As a result, the jets of any ideal will be homogeneous regardless
	    of the homogeneity of the base ideal, or that of its affine jets.
	Example
	    R= QQ[x,y,z]
	    I= ideal (y-x^2, z-x^3)
	    JI= jets(2,I)
	    isHomogeneous JI
	    JIproj= jets(2,I,Projective=>true)
	    isHomogeneous JIproj

Node
    Key
	(jets,ZZ,QuotientRing)
    Headline
    	the jets of an affine algebra
    Usage
    	jets (n,Q)
    Inputs
	n:ZZ
	Q:QuotientRing
    Outputs
        :QuotientRing
    Description
    	Text
    	    This function is provided by the package @TO Jets@.  Forms the jets of a @TO QuotientRing@ by forming the quotient of
	    @TO (jets,ZZ,PolynomialRing)@ of the ambient ring of @TT "Q"@ with 
	    @TO (jets,ZZ,Ideal)@ of the ideal defining @TT "Q"@
    	Example	    
	    R= QQ[x,y];
	    I= ideal(y^2-x^3);
    	    Q= R/I;
	    JQ= jets(2,Q);
	    describe JQ
    Caveat
    	Forming quotients triggers a Groebner basis computation, which may be time consuming.
	
Node
    Key
	(jets,ZZ,RingMap)
    Headline
    	the jets of a homomorphism of rings
    Usage
    	jets (n,f)
    Inputs
	n:ZZ
	f:RingMap
    Outputs
        :RingMap
	    obtained by applying the @TT "n"@-th jets functor to @TT "f"@
    Description
    	Text
	    This function is provided by the package
	    @TO Jets@.
    	Example	    
	    R= QQ[x,y,z]
	    S= QQ[t]
	    f= map(S,R,{t,t^2,t^3})
	    Jf= jets(2,f);
	    matrix Jf
    	Text
	    This function can also be applied when the source and/or the target
	    of the ring homomorphism are quotients of a polynomial ring
    	Example
	    I= ideal(y-x^2,z-x^3)
	    Q= R/I
	    g= map(S,Q,{t,t^2,t^3})
	    isWellDefined g
	    Jg= jets(2,g);
	    isWellDefined Jg

Node
    Key
	(jets,ZZ,Graph)
	(jets,ZZ,HyperGraph)
    Headline
    	the jets of a graph
    Usage
    	jets (n,G)
    Inputs
	n:ZZ
	G:Graph
	    undirected, finite, and simple graph or hypergraph
    Outputs
        :Graph
	 the (hyper)graph of @TT "n"@-jets of @TT "G"@
    Description
    	Text
	    This function is provided by the package
	    @TO Jets@.
	    
	    Jets of graphs are defined in § 2 of
	    @arXiv("2104.08933","F. Galetto, E. Helmick, and M. Walsh,
    		Jet graphs")@.
	    The input is of type @TO "EdgeIdeals::Graph"@ as defined by
	    the @TO EdgeIdeals@ package, which is automatically exported
	    when loading @TO Jets@.
    	Example	    
	    R= QQ[x,y,z]
	    G= graph(R,{{x,y},{y,z}})
	    JG= jets(2,G)
	    vertexCovers JG
	Text
	    We can also calculate the jets of a  @TO "EdgeIdeals::HyperGraph"@.
	Example
	    R= QQ[u,v,w,x,y,z]
	    H= hyperGraph(R,{{u},{v,w},{x,y,z}})
    	    jets(1,H)

Node
    Key
    	jet
    Headline
    	hashtable key
    Description
    	Text
	    @TO CacheTable@ for storing information on jets constructed
	    from a base object @TT "x"@.
	    For @TO PolynomialRing@ and @TO QuotientRing@, stored as @TT "x.*"@.
	    For @TO RingMap@ and @TO Ideal@ stored as @TT "x.cache.*"@.
    SeeAlso
	projet
	jetsRing
	jetsMaxOrder
	jetsMatrix
	jetsBase
    	jetsInfo

Node
    Key
    	projet
    Headline
    	hashtable key
    Description
    	Text
	    @TO CacheTable@ for storing information on the projective jets
	    of the base object @TT "x"@.
	    For @TO PolynomialRing@ and @TO QuotientRing@, stored as @TT "x.*"@.
	    For @TO RingMap@ and @TO Ideal@ stored as @TT "x.cache.*"@.
    SeeAlso
    	jet
	jetsRing
	jetsMaxOrder
	jetsMatrix
	jetsBase
    	jetsInfo

Node
    Key
    	jetsRing
    Headline
    	hashtable value
    Description
    	Text
    	    The @TO (jets,ZZ,PolynomialRing)@ of highest order computed thus far 
	    for a particular base ring.  Stored in @TO jet@ or @TO projet@ 
	    of the base.
    SeeAlso
    	jet
	projet
	jetsMaxOrder
	jetsMatrix
	jetsBase
    	jetsInfo	

Node
    Key
    	jetsMatrix
    Headline
    	hashtable value
    Description
    	Text
	    A matrix of jets elements which generate a @TO (jets,ZZ,Ideal)@
	    or serve as targets for a @TO (jets,ZZ,RingMap)@.  Stored in 
	    @TO jet@ or @TO projet@ of the base.
    SeeAlso
    	jet
	projet
	jetsRing
	jetsMaxOrder
	jetsBase
    	jetsInfo
		
Node
    Key
    	jetsMaxOrder
    Headline
    	hashtable value
    Description
    	Text
	    The highest order of jets computed thus far for a particular 
	    object.  Stored in @TO jet@ or @TO projet@ of the base object.
    SeeAlso
    	jet
	projet
	jetsRing
	jetsMatrix
	jetsBase
    	jetsInfo	

Node
    Key
    	jetsBase
    Headline
    	hashtable value
    Description
    	Text
    	    The base ring of a @TO (jets,ZZ,PolynomialRing)@.  Stored in a jets object 
	    for reference.
    SeeAlso
    	jet
	projet
	jetsRing
	jetsMaxOrder
	jetsMatrix
    	jetsInfo
	
Node
    Key
    	jetsInfo
    Headline
    	hashtable key
    Description
    	Text
    	    @TO CacheTable@ for storing information on the base object within
	    the jets object.
    SeeAlso
    	jet
	projet
	jetsRing
	jetsMatrix
	jetsBase
    	jetsMaxOrder

Node
    Key
    	[jets,Projective]
   	[jetsProjection,Projective]
    Description
    	Text
	    Use projective case degrees for varibales in jets objects.(cite Vojta)
	    
Node
    Key
    	jetsRadical
    Headline
    	compute radical jets ideal 
    Subnodes
    	(jetsRadical,ZZ,Ideal)
	
Node
    Key
    	(jetsRadical,ZZ,Ideal)
    Usage
    	jetsRadical(n,I)
    Inputs
    	n:ZZ
	I:Ideal
    Outputs
        :Ideal
    	    radical of the nth jets of @TT "I"@
    Description
   	Text
	    This function is provided by the package @TO Jets@. It returns the radical
	    of the ideal of jets of the input ideal.
	    
	    If the input is not a monomial ideal, this function uses the @TO radical@ function from
	    the @TO MinimalPrimes@ package.

	    If the input is a monomial ideal, it uses an algorithm 
	    based on the proof of Theorem 3.2 in @HREF("https://doi.org/10.1080/00927870500454927",
	    "R.A. Goward and K.E. Smith, The jet scheme of a monomial scheme")@.
	    This has the potential to speed up the computation, especially for large jet orders.
	    Note that the generating set of the output may not be minimal,
	    unless the generators of the input are squarefree monomials.
	    
	    An ideal generated by squarefree monomials:
	Example
	    R= QQ[x,y,z]
	    I= ideal (x*z, y*z)
	    J= jets(1,I); 
	    MP= radical J;
	    GS= jetsRadical(1,I);
	    netList sort MP_* | netList sort GS_*
    	Text
	    An ideal with genereators which are not squarefree:
	Example
	    R= QQ[x,y,z]
	    I= ideal(x*y^2, z*x, x^3)
	    J= jets(1,I); 
	    MP= radical J;
	    GS= jetsRadical(1,I);
	    netList sort MP_* | netList sort GS_*
	    MP == GS

Node
    Key
    	jetsProjection
    Headline
    	a map between jets rings
    Subnodes
    	(jetsProjection,ZZ,ZZ,PolynomialRing)
	
Node
    Key
    	(jetsProjection,ZZ,ZZ,PolynomialRing)
	(jetsProjection,ZZ,ZZ,QuotientRing)
    Headline
    	computes projection map
    Usage
    	jets(t,s,R)
	jets(t,s,Q)
    Inputs
    	t:ZZ
	s:ZZ
	R:PolynomialRing
	    or a quotient of
    Outputs
    	:RingMap
	 between jets orders
    Description
    	Text
	    This function is provided by the package @TO Jets@.  Generates an 
	    inclusion map from the order @TT "s"@ into the order @TT "t"@ jets
	    of a (quotient of a) polynomial ring.
	    Throws an error if @TT "t<s"@.
	    
    	Example
	    R=QQ[x,y]
	    f= jetsProjection(5,2,R)
	    use jets(2,R)
	    p= (x2 + 2*x1*y1 + x0*y2^2)
	    f p

Node
    Key
    	principalComponent
    	(principalComponent,ZZ,Ideal)
    Headline
    	computes principal component of jets
    Usage
    	principalComponent(s,I)
    Inputs
	s:ZZ
	I:Ideal
    Outputs
    	:Ideal
	 whose vanishing locus is the principal component of the @TT "s"@-jets of @TT "I"@
    Description
    	Text
	    This function is provided by the package @TO Jets@.
	    
	    Consider an affine variety $X \subseteq \mathbb{A}^n_\Bbbk$.
	    The principal (or dominant) component of the $s$-jets of $X$
	    is the Zariski closure of the $s$-jets of the smooth locus of $X$.
	    Let $X_{\mathrm{reg}}$ and $X_{\mathrm{sing}}$ denote respectively
	    the smooth and singular locus of $X$. If $\mathcal{J}_s$ denotes
	    the $s$-jets functor, then there is a natural embedding
	    $$X_\mathrm{sing} \subset X \subseteq \mathbb{A}^n_\Bbbk \subset
	    \mathcal{J}_s (\mathbb{A}^n_\Bbbk) \cong \mathbb{A}^{n(s+1)}_\Bbbk.$$
	    Let $I$ denote the ideal of $X_\mathrm{sing}$ in this embedding,
	    and let $J$ denote the ideal of $\mathcal{J}_s (X)$; both ideals
	    live in the polynomial ring $\Bbbk [\mathbb{A}^{n(s+1)}_\Bbbk]$.
	    We have an equality of sets $$\mathcal{J}_s (X_\mathrm{reg}) =
	    \mathcal{J}_s (X) \setminus X_\mathrm{sing} = \mathbf{V} (J)
	    \setminus \mathbf{V} (I).$$ By Theorem 10 in Chapter 4, §4 of
	    @HREF("https://doi.org/10.1007/978-3-319-16721-3",
		"D.A. Cox, J. Little, D. O'Shea - Ideals, Varieties, and Algorithms")@,
	    if $\Bbbk$ is algebraically closed, then there is an equality
	    $$\mathbf{V} (J\colon I^\infty) = \overline{\mathbf{V} (J)
	    \setminus \mathbf{V} (I)} = \overline{\mathcal{J}_s (X_\mathrm{reg})}.$$
	    This function returns the ideal $J\colon I^\infty$.
	    
	    As an example, consider the union of three non parallel lines
	    in the affine plane. We compute the principal component of the
	    jets of order two.
    	Example
	    R=QQ[x,y]
	    I=ideal(x*y*(x+y-1))
	    PC=principalComponent(2,I)
    	Text
	    Despite the name, the principal component need not be a component
	    of the jet scheme (i.e., it need not be irreducible). In this example,
	    the principal component has degree 3 and is the union of three components
	    of degree 1.
    	Example
	    P=primaryDecomposition jets(2,I)
	    any(P,c -> c==PC)
	    PC==intersect(select(P,c -> degree c==1))

Node
    Key
    	JJ
    Headline
    	scripted functor associated with jets
    Usage
    	JJ_n X
    Inputs
    	n:ZZ
    Description
    	Text
	    Shorthand for @TO jets@
	Example
	    R= QQ[x,y]
	    I= ideal(y^2-x^3)
	    JJ_2 R
	    JJ_2 I

Node
    Key
    	"Examples of functionality"
    Headline
    	some examples
    Description
    	Text
	    @TO (jetsRadical,ZZ,Ideal)@ can potentially speed up the calculation
	    of radical ideals of jets ideals
	Example
	    R=QQ[x,y,z]
	    I= ideal(x*y^2, z*x, x^3)
	    JI=jets(4,I);
	    elapsedTime jetsRadical(4,I);
	    elapsedTime radical JI;
///
end
