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
     Headline => "compute jet functors",
     PackageImports => {"SimpleDoc"},
     DebuggingMode => true
     )

-- all user facing symbols, methods, and types must be exported
importFrom(MinimalPrimes, {"radical"});


export {
    "jets",
    "maxOrder",
    "jetsBase",
    "jetsRing",
    "projet",
    "jet",
    "jetsMatrix",
    "jetsRadical",
    "jetsProjection"
    }

opts= {
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
jetsDegrees= opts >> o -> R -> (
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

--------------------------------------------------------------------------
--method functions--------------------------------------------------------
--------------------------------------------------------------------------


--Jets (Main Method)------------------------------------------------------

jets= method(Options=>opts);

jets(ZZ,Ring):= o -> (n,R) -> (
    --name to assign hashtable stored in basering depending on whether
    --are working in the projective or affine case
    typeName:= if o.Projective then (projet) else (jet);
    jetDegs:= null;--initialize degree list for jets variables
    
    if not R#? typeName then (
	jetDegs= if o.Projective then degGenerator(0, R) else degrees R;
	R#typeName= new CacheTable from {
	    (symbol maxOrder)=> 0,
	    (symbol jetsRing)=> coefficientRing R[jetsVariables(0,R), 
		                                 Join=> false,
					 	 Degrees=> jetDegs],
	    }
	);
    m:= R#typeName#maxOrder;
    S:= R#typeName#jetsRing;
    
    --build jet ring tower incrementally up to order n
    --this is inefficient in the affine case
    if n<0 then error("jets order must be a non-negative integer");

    if n>m then (
	for i from m+1 to n do(
    	    jetDegs= if o.Projective then degGenerator(i,R) else degrees R; 
	    S= S[jetsVariables(i,R), 
		Join=> false, 
		Degrees=> jetDegs];
            );
     	R#typeName#maxOrder= n;
	R#typeName#jetsRing= S;
	) else if m>n then (
	for i from 0 to m-n-1 do (
	    S= coefficientRing S;
	    )
	);
    
    S#jet= new CacheTable from {
	(symbol jetsBase)=> R,
	(symbol Projective)=> o.Projective
	}; 
    return S;
    )

jets(ZZ,Ideal):= o -> (n,I) -> (
    R:= ring I;
    S:= null;--initializes jets ring
    t:= local t;--initializes truncation variable
    
    typeName:= if o.Projective then (projet) else (jet);
    
    if not I.cache#? typeName then (
	S= jets(0,R, Projective=> o.Projective);
	I.cache#typeName= new CacheTable from {
	    (symbol maxOrder)=> 0,
	    (symbol jetsMatrix)=> (map(S,R,vars S)) gens I
	    };
    	);
   
    m:= I.cache#typeName#maxOrder;
    if n<0 then error("jets order must be a non-negative integer");
    
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
	(d,c):= coefficients(phi gens I);
	resultMatrix:= lift(c,S);
    	
	--update value in ideal cache
	I.cache#typeName#jetsMatrix= resultMatrix;
	I.cache#typeName#maxOrder= n;
	m=n;
	);
   
    --retrieve ideal of appropriate order
    JMatrix:= I.cache#typeName#jetsMatrix; 
    ideal (JMatrix)^{m-n..m}
    )

--how to store ideal information we caculate here?
jets(ZZ,RingMap):= o -> (n,phi) -> (
    I:= ideal(phi.matrix);
    typeName:= if o.Projective then (projet) else (jet);
    JR:= jets(n,phi.source, Projective=> o.Projective);
    JS:= jets(n,phi.target, Projective=> o.Projective);
    targets:= null;
    jets(0,I,Projective=> o.Projective);
    
    if (not phi.cache#? typeName) then (
	phi.cache#typeName= new CacheTable from {
	    (symbol maxOrder)=> 0,
    	    (symbol jetsMatrix)=> map(JS,JR,I.cache#typeName#jetsMatrix)
	    };
	);
    
    m:= phi.cache#typeName#maxOrder;
    
    if m < n then (
	jets(n,I, Projective=> o.Projective);
    	targets= (I.cache#typeName#jetsMatrix);	
    	) else (
    	targets= phi.cache#typeName#jetsMatrix^{m-n..m};
	);

    psi:= map(JS,JR,
	flatten transpose targets)
--	DegreeLift=> degreeLift,
--	DegreeMap=> degreeMap);
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
jetsProjection= method(Options=>opts);

jetsProjection(ZZ,ZZ,Ring):= o -> (t,s,R) -> (

    if t < s then error("whoops");    
    if t<0 or s<0 then error("jets orders must be non-negative integers");

    (map(jets(t,R,Projective=> o.Projective),jets(s,R,Projective=> o.Projective)))
    ) 


----------------------------------------------------------------------
-- Documentation
----------------------------------------------------------------------

beginDocumentation()

doc ///

Node
    Key
    	Jets
    Headline
    	Method for applying jets functor to various objects	
    Subnodes
    	jets
	jetsProjection
	jetsRadical
	[jets,Projective]
	"Storing Computations"

Node
    Key
    	jets
    Headline
    	Compute the jets of an object
    Subnodes	
	(jets,ZZ,Ring)
	(jets,ZZ,Ideal)
	(jets,ZZ,RingMap)
	
Node
    Key
    	"Storing Computations"
    Description
    	Text
	    After the jets of an object are computed, some elements are 
	    stored in a @TO CacheTable@ which, in turn, is stored in the 
	    parent object.  
    	Example
	    R= QQ[x,y]
	    I= ideal (x^2 - y)
	    jets(3,I)
	    keys I.cache.jet
    Subnodes
	jet
	projet
	jetsRing
	maxOrder
	jetsMatrix
	jetsBase    


Node
    Key
	(jets,ZZ,Ring)
    Headline
    	compute jets of a polynomial ring
    Usage
    	jets (n,R)
    Inputs
    	n:ZZ
    	R:Ring
    Outputs
    	:Ring
       	 of jets order @TT "n"@.
    Description
    	Text
	    This function is provided by the package @TO Jets@.  Rings are 
	    constructed incrementally as towers.  The function returns the 
	    ring with variables in the jets order requested, and coeffients 
	    in all lower orders.  
    	Example	    
	    R= QQ[x,y,z]
	    JR= jets(2,R)
	    describe JR

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
	    R= QQ[x,y,z]
	    I= ideal (x*z-y^2)
    	    jets(4,I)
    	    I.cache#jet#jetsMatrix

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
	    R= QQ[x,y]
	    S= QQ[a,b,c]
	    f= map(S,R,{a^2-b^2, a*c-b^2})
	    Jf= jets(2,f)
	    Jf (y1 + 2*x2^2 + x0*y0)

Node
    Key
    	jet
    Headline
    	hashtable key
    Description
    	Text
	    @TO CacheTable@ for storing information on jets constructed
	    from a base object.  For @TO Ring@, stored as @TT "x.*"@  For 
	    @TO RingMap@ and @TO Ideal@ stored as @TT "x.cache.*"@  Also used
	    to store basic information in @TO (jets,ZZ,Ring)@.
    SeeAlso
	projet
	jetsRing
	maxOrder
	jetsMatrix
	jetsBase

Node
    Key
    	projet
    Headline
    	hashtable key
    Description
    	Text
	    @TO CacheTable@ for storing information on the projective 
	    jets of the base object.  For @TO Ring@, stored as @TT "x.*"@.  
	    For @TO RingMap@ and @TO Ideal@ stored as @TT "x.cache.*"@
    SeeAlso
    	jet
	jetsRing
	maxOrder
	jetsMatrix
	jetsBase

Node
    Key
    	jetsRing
    Headline
    	hashtable value
    Description
    	Text
    	    The @TO (jets,ZZ,Ring)@ of highest order computed thus far 
	    for a particular base ring.  Stored in @TO jet@ or @TO projet@ 
	    of the base.
    SeeAlso
    	jet
	projet
	maxOrder
	jetsMatrix
	jetsBase

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
	maxOrder
	jetsBase

Node
    Key
    	maxOrder
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

Node
    Key
    	jetsBase
    Headline
    	hashtable value
    Description
    	Text
    	    The base ring of a @TO (jets,ZZ,Ring)@.  Stored in a jets object 
	    for reference.
    SeeAlso
    	jet
	projet
	jetsRing
	maxOrder
	jetsMatrix

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
	 generated by the jets of the generators of @TT "I"@.
    Description
   	Text
	    A shortcut to calculate radical jets of a monomial ideal
	    (cite article of Goward and Smith).  If the 
	    input is not a monomial ideal this function uses the @TO radical@ function from
	    the @TO MinimalPrimes@ package.

Node
    Key
    	jetsProjection
    Headline
    	a map between jets rings
    Subnodes
    	(jetsProjection,ZZ,ZZ,Ring)
	
Node
    Key
    	(jetsProjection,ZZ,ZZ,Ring)
    Headline
    	computes projection map
    Usage
    	jets(t,s,R)
    Inputs
    	t:ZZ
	s:ZZ
	R:Ring
    Outputs
    	:RingMap
	 between jets orders
    Description
    	Text
	    Generates an inclusion map from @TO (jets,ZZ,Ring)@ of order @TT "s"@ into
	    @TO (jets,ZZ,Ring)@ of order @TT "t"@.  Throws an error if @TT "t<s"@.
	    
    	Example
	    R=QQ[x,y]
	    f= jetsProjection(5,2,R)
	    use jets(2,R)
	    p= (x2 + 2*x1*y1 + x0*y2^2)
	    f p
	    
///

----------------------------------------------------------------------
-- TESTS
----------------------------------------------------------------------



end
