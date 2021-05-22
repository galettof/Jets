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


importFrom(MinimalPrimes, {"radical"});

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
        S= jets(n,ambient R, Projective=> o.Projective);
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
	I.cache#typeName#jetsMaxOrder= n;
	m=n;
	);
   
    --retrieve ideal of appropriate order
    JMatrix:= I.cache#typeName#jetsMatrix; 
    f:= map(jets(n,R,Projective=> o.Projective),jets(m,R, Projective=> o.Projective));
    J:= f promote(ideal (JMatrix)^{m-n..m},jets(n,R));

    J.cache#jetsInfo= new CacheTable from {
	jetsBase=> I,
	Projective=> o.Projective
	};
    
    return J;
    )

jets(ZZ,QuotientRing):= o -> (n,R) -> (
    splitQuotient:= presentation R;
    ambientRing:= ring splitQuotient;
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

jetsProjection(ZZ,ZZ,PolynomialRing):= o -> (t,s,R) -> (

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

----------------------------------------------------------------------
-- Documentation
----------------------------------------------------------------------
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
	(jets,ZZ,PolynomialRing)
	(jets,ZZ,Ideal)
	(jets,ZZ,QuotientRing)
	(jets,ZZ,RingMap)
	JJ
	
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
	    I= ideal (x^3 + y^3 - 3*x*y)
    	    J= jets(3,I);
    	    I.cache#jet#jetsMatrix
	    netList J_*

Node
    Key
	(jets,ZZ,QuotientRing)
    Headline
    	the jets of a @TO QuotientRing@
    Usage
    	jets (n,Q)
    Inputs
	n:ZZ
	Q:QuotientRing
    Outputs
        :QuotientRing
    Description
    	Text
    	    forms the jets of a @TO QuotientRing@ by forming the quotient of
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
	 generated by the jets of the generators of @TT "I"@.
    Description
   	Text
	    A shortcut to calculate radical jets of a monomial ideal
	    (cite article of Goward and Smith).  If the 
	    input is not a monomial ideal this function uses the @TO radical@ function from
	    the @TO MinimalPrimes@ package.  Note: this method will not necessarily return
	    minimal generators unless the generators of the input are squarefree
	    monomials.

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
    Headline
    	computes projection map
    Usage
    	jets(t,s,R)
    Inputs
    	t:ZZ
	s:ZZ
	R:PolynomialRing
    Outputs
    	:RingMap
	 between jets orders
    Description
    	Text
	    Generates an inclusion map from @TO (jets,ZZ,PolynomialRing)@ of order @TT "s"@ into
	    @TO (jets,ZZ,PolynomialRing)@ of order @TT "t"@.  Throws an error if @TT "t<s"@.
	    
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
    	Scripted functor assosiated with @TO jets@
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
///
end
