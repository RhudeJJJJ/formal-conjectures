"""Exact candidate arithmetic for the existing general mean-shift Lean checkers.

These rational computations produce data. Only the Lean identities and
inequality certificates establish a theorem about the actual matrices.
"""
import math
from fractions import Fraction as F

def trim(p):
    p=list(map(F,p))
    while p and not p[-1]:p.pop()
    return p
def add(p,q):return trim([(p[i] if i<len(p) else 0)+(q[i] if i<len(q) else 0) for i in range(max(len(p),len(q)))])
def neg(p):return [-c for c in p]
def sub(p,q):return add(p,neg(q))
def mul(p,q):
    r=[F(0)]*max(0,len(p)+len(q)-1)
    for i,a in enumerate(p):
        for j,b in enumerate(q):r[i+j]+=a*b
    return trim(r)
def smul(c,p):return trim([c*v for v in p])
def sq(p):return mul(p,p)
def comp(p,q):
    r=[]
    for c in reversed(p):r=add([c],mul(q,r))
    return r
def evaluate(p,x):
    r=0
    for c in reversed(p):r=r*x+c
    return r
def derivative(p):return trim([i*p[i] for i in range(1,len(p))])
def primitive(p):return [F(0)]+[c/F(i+1) for i,c in enumerate(p)]
def bern(p,a,b,d):
    c=comp(p,[a,b-a]);assert len(c)<=d+1
    return [sum((c[k]*F(math.comb(j,k),math.comb(d,k)) for k in range(min(j,len(c)-1)+1)),F(0)) for j in range(d+1)]
def path(x,n):
    a,b=[F(-1)],[];z=[x,F(1)]
    for _ in range(n):a,b=sub(b,a),sub(mul(sub(z,[1]),b),mul(z,a))
    return a,b
def parts(p):
    r=[F(0)]*len(p);im=[F(0)]*len(p)
    for j,c in enumerate(p):
        if j%2:im[j]=(-1 if j%4==3 else 1)*c
        else:r[j]=(-1 if j%4==2 else 1)*c
    return trim(r),trim(im)
def pack(x,p,q):
    ap,dp=path(x,p+1);aq,dq=path(x,q+1);ar,dr=path(x,p+q+2)
    A=mul(sub(dp,ap),sub(dq,aq));B=sub(sub(smul(2,mul(dp,dq)),mul(ap,dq)),mul(aq,dp));C=sub(dr,ar)
    H=[F(-1),2*(x-1),F(2)];W=[F(0),F(2)]
    BB=sub(mul(A,H),mul(W,B));EE=sub(mul(C,H),mul(W,dr))
    a,ai=parts(A);b,bi=parts(BB);c,ci=parts(C);e,ei=parts(EE)
    U=add(sq(sub(sub(add(mul(b,e),mul(bi,ei)),mul(a,c)),mul(ai,ci))),sq(add(sub(sub(mul(bi,e),mul(b,ei)),mul(ai,c)),mul(a,ci))))
    V=add(sq(add(sub(sub(mul(a,e),mul(ai,ei)),mul(b,c)),mul(bi,ci))),sq(sub(sub(add(mul(a,ei),mul(ai,e)),mul(b,ci)),mul(bi,c))))
    N=sub(add(sq(b),sq(bi)),add(sq(a),sq(ai)));E=sub(add(sq(e),sq(ei)),add(sq(c),sq(ci)))
    return dict(as_=A,bs=BB,cs=C,es=EE,us=U,vs=V,js=sq(N),ns=N,sep=E)
def series(t,n):return sum((t**(2*i+1)/F(2*i+1) for i in range(n)),F(0))
def error(t,n):return t**(2*n+1)/(1-t*t)
def log_payment(c,terms=48,denominator=10**14):
    assert c>0;k=0
    while 2**k*c<1:k+=1
    v=2**k*c;t=(v-1)/(v+1)
    lower=series(t,terms)-k*(series(F(1,3),terms)+error(F(1,3),terms))
    return F((lower*denominator).__floor__(),denominator),k,terms
def q(v):
    v=F(v);return str(v.numerator) if v.denominator==1 else f'({v.numerator}/{v.denominator})'
def ls(p):return '['+','.join(q(c) for c in p)+']'
def vec(p):return '!['+','.join(q(c) for c in p)+']'
