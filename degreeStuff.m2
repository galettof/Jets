load "jetsMethod.m2"

R0=QQ[x,y,z];
I0= ideal(x^2*y, y*z^2);

R1=QQ[x,y,z,Degrees=>{2,2,2}];
I1= ideal(x^2*y, y*z^2);

R2=QQ[x,y,z,Degrees=>{{2,1,2},{2,1,2},{2,1,2}}];
I2= ideal(x^2*y, y*z^2);

m=-1;
n=2;


opts={Projective=> false}

--returns a sequence (degrees of T vars, degree map for phi)
jetsDegrees= opts >> o -> R -> (
    Tdegrees:= null;
    degreeMap:= null;
    
    if o.Projective then (
	Tdegrees= -1 * {degree R_1};
	degreeMap= d -> degree 1_R;
	) else (
	Tdegrees= {degree 1_R};
	degreeMap= identity;
	);
    return (Tdegrees, degreeMap);
    )

jetsp= opts >> o -> (n,I) -> (
    R:= ring I;
    (Tdegrees, degreeMap):= jetsDegrees (R, Projective=> o.Projective);
    S:= jets(n,R, Projective=> o.Projective);
    T:= S[t,Degrees=> Tdegrees, Join=> false]/(ideal(t^(n+1)));--determine deg of tb
    tempS:= S;
    Tpolys:= reverse join(
	(for i from 0 to n-1 list( 
		promote(matrix t^(n-i),T) * vars tempS
		) do (
		tempS= coefficientRing tempS)),
	{promote (matrix t^0,T) * vars tempS}
	);
    phi:= map(T,R,sum Tpolys, DegreeMap=> degreeMap);--need better deg map
    (d,c):= coefficients(phi gens I,Monomials=> (basis T)_{0..n});--m+1..n});
    result:= lift(c,S)
)
end
