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
    "jetsInfo"
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
	    
	    Additional features include an option for jets with
	    "projective" gradings, an alternative algorithm to compute
	    the radical of jets of monomial ideals, and a function
	    to construct jets of graphs.
    References
    	@arXiv("math/0612862","L. Ein and M. Mustaţă.
    		Jet schemes and singularities.")@
		
    	@arXiv("2104.08933","F. Galetto, E. Helmick, and M. Walsh.
    		Jet graphs.")@
		
    	@HREF("https://doi.org/10.1080/00927870500454927",
	    "R.A. Goward and K.E. Smith.
	    The jet scheme of a monomial scheme.")@

    	@arXiv("math/0407113","P. Vojta.
	    	Jets via Hasse-Schmidt Derivations.")@
    Subnodes
    	jets
	jetsProjection
	jetsRadical
	[jets,Projective]
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
	    in all lower orders.  Grading follows that of the base ring.  
    	Example	    
	    R= QQ[x,y,z,Degrees=>{2,1,3}]
	    JR= jets(2,R)
	    describe JR
    	    degrees (flattenRing JR)_0	    
    	Text
	    When the @TO [jets,Projective]@ option is set to true, the degree 
	    of each jets variable matches the jets order.
    	Example
	    R=QQ[x,y,z,Degrees=>{2,1,3}]
	    JR= jets(2,R,Projective=>true)
	    degrees (flattenRing JR)_0
	    	  
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
	    of each jets variable matches its order (cite notes of Vojta).  
	    As a result, the jets of any ideal will be homogeneous regardless
	    of the homogeneity of the base ideal, or that of its affine jets.
	Example
	    R= QQ[x,y,z]
	    I= ideal (y-x^2, z-x^3)
	    JI= jets(2,I);
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
    	    ambient JQ
	    ideal JQ

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
	 a map from a ring @TT "R"@ to a ring @TT "S"@
    Outputs
        :RingMap
	 from the jets of order @TT "n"@ of ring @TT "R"@ to the jets of order 
	 @TT "n"@ of a ring @TT "S"@
    Description
    	Text
	    This function is provided by the package
	    @TO Jets@.
    	Example	    
	    R= QQ[x,y,z]
	    S= QQ[t]
	    f= map(S,R,{t,t^2,t^3})
	    Jf= jets(2,f);
	    Jf y1
	    f.cache#jet#jetsMatrix

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
	 the graph of jets of @TT "G"@
    Description
    	Text
	    This function is provided by the package
	    @TO Jets@.  Extends from the @TO EdgeIdeals@ package.
    	Example	    
	    R= QQ[x,y,z]
	    G= graph(R,{{x,y},{y,z}})
	    jets(2,G)
	Text
	    We can also calculate the jets of a hypergraph
	Example
	    R= QQ[x,y,z,w]
	    H= hyperGraph(R,{{x,y,z},{x,w,z},{w,x,y}})
    	    jets(2,H)

Node
    Key
    	jet
    Headline
    	hashtable key
    Description
    	Text
	    @TO CacheTable@ for storing information on jets constructed
	    from a base object.  For @TO PolynomialRing@, stored as @TT "x.*"@  For 
	    @TO RingMap@ and @TO Ideal@ stored as @TT "x.cache.*"@  Also used
	    to store basic information in @TO (jets,ZZ,PolynomialRing)@.
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
	    @TO CacheTable@ for storing information on the projective 
	    jets of the base object.  For @TO PolynomialRing@, stored as @TT "x.*"@.  
	    For @TO RingMap@ and @TO Ideal@ stored as @TT "x.cache.*"@
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
	    This function is provided by the package @TO Jets@.  A shortcut to calculate 
	    radical jets of a monomial ideal (cite article of Goward and Smith).  If the 
	    input is not a monomial ideal this function uses the @TO radical@ function from
	    the @TO MinimalPrimes@ package.  Note: this method will not necessarily return
	    minimal generators unless the generators of the input are squarefree
	    monomials.
	Text 
	    An ideal generated by squarefree monomials
	Example
	    R= QQ[x,y,z]
	    I= ideal (x*z, y*z)
	    J= jets(1,I); 
	    MP= radical J;
	    GS= jetsRadical(1,I);
	    netList sort MP_* | netList sort GS_*
    	Text
	    An ideal with genereators which are not squarefree
	Example
	    R= QQ[x,y,z]
	    I= ideal(x*y^2, z*x, x^3)
	    J= jets(1,I); 
	    MP= radical J;
	    GS= jetsRadical(1,I);
	    netList sort MP_* | netList sort GS_*

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
	    inclusion map from @TO (jets,ZZ,PolynomialRing)@ of order @TT "s"@ into
	    @TO (jets,ZZ,PolynomialRing)@ of order @TT "t"@.  Throws an error 
	    if @TT "t<s"@.
	    
    	Example
	    R=QQ[x,y]
	    f= jetsProjection(5,2,R)
	    use jets(2,R)
	    p= (x2 + 2*x1*y1 + x0*y2^2)
	    f p

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
	    @TO (jetsRadical,ZZ,Ideal)@ can significanly speed up the calculation
	    of radical ideals of jets ideals
	Example
	    R=QQ[x,y,z]
	    I= ideal(x*y^2, z*x, x^3)
	    JI=jets(4,I);
	    elapsedTime jetsRadical(4,I);
	    elapsedTime radical JI;
///
end
