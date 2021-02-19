restart
load "jetsMethod.m2"
load "helpers.m2"

R=QQ[x,y]
f=x^2*y
g=x+y
I= ideal(f,g)
X= Spec(R/I)

A= arcs(X)
n=4
jets(7,A)





