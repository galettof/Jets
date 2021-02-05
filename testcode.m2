restart
load "jetsMethod.m2"

R= QQ[x,y,z]
f1= x*y
f2= x*z
f3= y*z

I1= ideal f1
I2= ideal(f1,f2)
I3= ideal(f1,f2,f3)

J1= jets(1,I1,ReturnVector=> true)
J2= jets(1,I2,ReturnVector=> true)
J3= jets(1,I3,ReturnVector=> true)

I4= ideal(x*y*z)
J4= jets(1,I4,ReturnVector=> true)

Ix= ideal x
Iy= ideal y
Iz= ideal z

Jx= jets(1,Ix,ReturnVector=> true)
Jy= jets(1,Iy,ReturnVector=> true)
Jz= jets(1,Iz,ReturnVector=> true)
