"""Exact mirror of the kernel-checked Expr compiler and reciprocal transform.

This is a data producer. Every emitted identity and sign requires Lean checking.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from math import comb
from functools import lru_cache

def zero(n):return Q(0) if n==0 else []
def const(n,c):return Q(c) if n==0 else [const(n-1,c)]
def coord(n,i):return [zero(n-1),const(n-1,1)] if i==0 else [coord(n-1,i-1)]
def plus(n,p,q):
    if not n:return p+q
    return [plus(n-1,p[i],q[i]) if i<len(p) and i<len(q) else (p[i] if i<len(p) else q[i]) for i in range(max(len(p),len(q)))]
def scaled(n,c,p):return c*p if n==0 else [scaled(n-1,c,x) for x in p]
def times(n,p,q):
    if not n:return p*q
    if not p:return []
    return plus(n,[times(n-1,p[0],d) for d in q],[zero(n-1)]+times(n,p[1:],q))
def power(n,p,k):return const(n,1) if k==0 else times(n,p,power(n,p,k-1))

@dataclass
class Program:
    degree:int
    direct:list
    reciprocal:list

def rat(c):
    p=const(3,Q(c));return Program(0,p,p)
def variable(i):return Program(1 if i==0 else 0,coord(3,i),const(3,1) if i==0 else coord(3,i))
def add(a,b):
    d=max(a.degree,b.degree)
    inverse=plus(3,times(3,a.reciprocal,power(3,coord(3,0),d-a.degree)),times(3,b.reciprocal,power(3,coord(3,0),d-b.degree)))
    return Program(d,plus(3,a.direct,b.direct),inverse)
def scale(c,a):return Program(a.degree,scaled(3,c,a.direct),scaled(3,c,a.reciprocal))
def sub(a,b):return add(a,scale(Q(-1),b))
def mul(a,b):return Program(a.degree+b.degree,times(3,a.direct,b.direct),times(3,a.reciprocal,b.reciprocal))
def pw(a,k):return Program(a.degree*k,power(3,a.direct,k),power(3,a.reciprocal,k))
def csub(a,b):return sub(a[0],b[0]),sub(a[1],b[1])
def cmul(a,b):return sub(mul(a[0],b[0]),mul(a[1],b[1])),add(mul(a[0],b[1]),mul(a[1],b[0]))
def star(a):return a[0],mul(rat(-1),a[1])
def norm(a):return add(pw(a[0],2),pw(a[1],2))

y=variable(0)
def den(c):
    if c==0:return rat(1)
    if c==1:return y
    if c==2:return add(pw(y,2),rat(1))
    if c==3:return add(pw(y,3),mul(rat(2),y))
    return mul(mul(y,add(add(pw(y,4),mul(rat(3),pw(y,2))),rat(1))),add(add(pw(y,4),mul(rat(4),pw(y,2))),rat(3)))
def num(c,i):
    if c==0:return y
    if c==1:return add(pw(y,2),rat(1))
    if c==2:return add(pw(y,3),mul(rat(2),y))
    if c==3:return add(add(pw(y,4),mul(rat(3),pw(y,2))),rat(1))
    return add(add(mul(mul(pw(y,2),add(add(pw(y,4),mul(rat(3),pw(y,2))),rat(1))),add(add(pw(y,4),mul(rat(4),pw(y,2))),rat(3))),mul(add(pw(y,4),mul(rat(2),pw(y,2))),add(add(pw(y,4),mul(rat(4),pw(y,2))),rat(3)))),variable(i))

@lru_cache(maxsize=1)
def programs(d,c1,c2):
    d=Q(d);l=mul(den(c1),den(c2));s=add(mul(num(c1,1),den(c2)),mul(num(c2,2),den(c1)));r=mul(num(c1,1),num(c2,2))
    a=(mul(rat(d),sub(r,l)),mul(rat(-d),s))
    b=(add(mul(mul(rat(2),y),add(mul(rat(2-d),sub(r,l)),mul(rat(4),l))),mul(rat(d),s)),add(add(mul(add(mul(rat(2),pw(y,2)),rat(d)),sub(r,l)),mul(mul(rat(2*d),y),s)),mul(mul(rat(4),pw(y,2)),l)))
    c=(mul(rat(d),add(r,l)),mul(rat(-d),sub(s,mul(y,l))))
    e=(add(mul(mul(mul(rat(2),y),rat(2-d)),add(r,l)),mul(rat(d),sub(s,mul(y,l)))),add(mul(add(mul(rat(2),pw(y,2)),rat(d)),add(r,l)),mul(mul(rat(2*d),y),sub(s,mul(y,l)))))
    return norm(csub(cmul(b,star(e)),cmul(a,star(c)))),norm(csub(cmul(a,e),cmul(b,c))),pw(sub(norm(b),norm(a)),2)

def gap(d,c1,c2,s,L):
    u,v,j=programs(d,c1,c2)
    return add(j,add(scale(-L*(1+s),u),scale(-L*(1+1/s),v)))

def terms(n,p,prefix=()):
    if not n:
        if p:yield prefix,p
        return
    for i,c in enumerate(p):yield from terms(n-1,c,prefix+(i,))
def degrees(n,p):
    out=[0]*n
    def walk(k,p):
        if not k:return
        out[n-k]=max(out[n-k],len(p)-1)
        for c in p:walk(k-1,c)
    walk(n,p);return out
def dense(n,rows,deg,prefix=()):
    if not n:return rows.get(prefix,Q(0))
    return [dense(n-1,rows,deg,prefix+(i,)) for i in range(deg[len(prefix)]+1)]
def affine_reference(p,l,w):
    deg=degrees(3,p);out={}
    for e,c in terms(3,p):
        for i in range(e[0]+1):
            for j in range(e[1]+1):
                for k in range(e[2]+1):
                    key=(i,j,k);v=c
                    for axis,t in enumerate(key):v*=comb(e[axis],t)*l[axis]**(e[axis]-t)*w[axis]**t
                    out[key]=out.get(key,Q(0))+v
    return dense(3,out,deg),deg

def affine(p,l,w):
    """Apply the same exact substitution one coordinate at a time.

    The dense degrees and zero padding are preserved for the Lean checker.
    Combining terms between coordinates avoids repeated rational powers.
    """
    deg=degrees(3,p);out=dict(terms(3,p))
    for axis,D in enumerate(deg):
        lp=[Q(1)];wp=[Q(1)]
        for _ in range(D):lp.append(lp[-1]*l[axis]);wp.append(wp[-1]*w[axis])
        weights=[[comb(e,j)*lp[e-j]*wp[j] for j in range(e+1)] for e in range(D+1)]
        new={}
        for e,c in out.items():
            for j,weight in enumerate(weights[e[axis]]):
                if not weight:continue
                key=list(e);key[axis]=j;key=tuple(key)
                new[key]=new.get(key,Q(0))+c*weight
        out={e:c for e,c in new.items() if c}
    return dense(3,out,deg),deg
def bernstein_nonnegative(p,deg):
    data=dict(terms(3,p))
    for axis,D in enumerate(deg):
        out={}
        for e,c in data.items():
            for j in range(e[axis],D+1):
                key=list(e);key[axis]=j;key=tuple(key)
                out[key]=out.get(key,Q(0))+c*Q(comb(j,e[axis]),comb(D,e[axis]))
        data=out
    return all(c>=0 for c in data.values())
def lean(n,p):
    if not n:return str(p.numerator) if p.denominator==1 else f'({p.numerator}/{p.denominator})'
    return '['+','.join(lean(n-1,c) for c in p)+']'
