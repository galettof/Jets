restart
load "jetsMethod.m2"
load "helpers.m2"

R=QQ[x,y]
f=x^2*y
g=x+y
I= ideal(f,g)
X= Spec(R/I)
A= arcs(X)

S=QQ[x,y,z]
a=x*y
b=x+z
J= ideal(a,b)
Y= Spec(S/J)
B= arcs(Y)












