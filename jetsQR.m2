load "jetsMethod.m2"

R0=QQ[x,y,z,w];
K= ideal(x,y,z)

I0= ideal x;
R1=R0/I0;

I1= ideal y;
R2=R1/I1;

I2= ideal z;
R3= R2/I2;

S=R0/K

jetsQ= {Projective=> true} >> o -> (n,R) -> (
    jetGens:= presentation R;
    I:= jets(n,ideal(jetGens));
    base:= ring I;
    base/I	
    )

end
restart
load "jetsQR.m2"





    


