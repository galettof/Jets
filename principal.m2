needsPackage "Jets"
principalComponent = method()
principalComponent(ZZ,Ideal) := (n,I) -> (
    R := ring I;
    JR := jets(n,R);
    JI := jets(n,I);
    p := jetsProjection(n,0,R);
    i := map(source p,R,vars source p);
    --compute the singular locus of I
    --map it to the zero jets via the map i
    --then to the n jets via the map p
    sing := p(i(ideal singularLocus I));
    -- need to saturate if I is not radical
    JI:sing
    )
