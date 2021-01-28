restart
R=QQ[x,y]
f=(x^2+1)*y-1
--define a ring map to get jets of order 3
--we go mod t^4 because we don't care about higher t powers
S=QQ[x0,x1,x2,x3,y0,y1,y2,y3,t] / ideal(t^4)
phi=map(S,R,{x0+x1*t+x2*t^2+x3*t^3,y0+y1*t+y2*t^2+y3*t^3})
--apply to f to get substitution
g=phi f
--extract coefficients with respect to t
(m,c)=coefficients(g,Variables=>{t})
J3=ideal c
netList J3_*
