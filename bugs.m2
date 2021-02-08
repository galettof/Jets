--- error with monimial in less than m variables
restart
load "jetsMethod.m2"
R= QQ[x,y]
f= x*y
I= ideal f
jets(0,I)

S= QQ[x,y,z]
g= x*y
I= ideal g
jets(0,I)
jets(1,I)
---works here though
restart
load "jetsMethod.m2"
R= QQ[x,y,z]
f= x*y
I= ideal f
jets(0,I)




--error with variable naming
restart
load "indexRing.m2"
R=QQ[z_(2,3)]
indexRing(0,R)


