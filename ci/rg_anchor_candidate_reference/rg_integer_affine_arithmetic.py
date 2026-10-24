"""Exact integer-scaled arithmetic for candidate production; Lean checks the witnesses."""
from functools import lru_cache
from fractions import Fraction as F
from math import comb,isqrt,lcm
from rg_mean_polynomial_arithmetic import trim

@lru_cache(maxsize=64)
def _integer_coefficients(p):
    denominator=lcm(*(x.denominator for x in p)) if p else 1
    return tuple(x.numerator*(denominator//x.denominator) for x in p),denominator

def coefficients(p):
    return _integer_coefficients(tuple(map(F,p)))

def evaluate(p,x):
    p=trim(p);x=F(x)
    if not p:return F(0)
    cs,den=coefficients(p);degree=len(cs)-1
    if not x:return F(cs[0],den)
    if x==1:return F(sum(cs),den)
    result=cs[-1];weight=x.denominator
    for c in reversed(cs[:-1]):
        result=result*x.numerator+c*weight;weight*=x.denominator
    return F(result,den*x.denominator**degree)

def compose_affine(p,a,w):
    p=trim(p);a,w=F(a),F(w)
    if not p:return []
    if not w:return trim([evaluate(p,a)])
    if not a and w==1:return p
    cs,den=coefficients(p);degree=len(cs)-1
    qden=lcm(a.denominator,w.denominator)
    A=a.numerator*(qden//a.denominator);W=w.numerator*(qden//w.denominator)
    ap=[1];wp=[1];qp=[1]
    for _ in range(degree):ap.append(ap[-1]*A);wp.append(wp[-1]*W);qp.append(qp[-1]*qden)
    common=den*qp[-1];out=[]
    for k in range(degree+1):
        value=sum((cs[i]*comb(i,k)*ap[i-k]*qp[degree-i] for i in range(k,degree+1) if cs[i]),0)
        out.append(F(wp[k]*value,common))
    return trim(out)

@lru_cache(maxsize=32)
def _bernstein_weights(degree):
    ds=[comb(degree,i) for i in range(degree+1)]
    common=lcm(*ds)
    return common,tuple(tuple(comb(j,i)*(common//ds[i]) for i in range(j+1)) for j in range(degree+1))

def bernstein(p,a,b,degree):
    assert degree>=0
    values=compose_affine(p,F(a),F(b)-F(a))
    assert len(values)<=degree+1
    cs,den=coefficients(values);common,weights=_bernstein_weights(degree)
    return [F(sum((cs[i]*row[i] for i in range(min(len(cs),len(row)))),0),den*common) for row in weights]

def dyadic_sqrt(value,bits=42):
    value=F(value);assert value>=0
    if not value:return F(1,2**128)
    exponent=(value.numerator.bit_length()-value.denominator.bit_length())//2
    scale=F(2)**(bits-exponent)
    v=value*scale*scale
    return F(isqrt(v.numerator//v.denominator))/scale
