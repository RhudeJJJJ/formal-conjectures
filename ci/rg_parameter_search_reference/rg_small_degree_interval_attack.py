#!/usr/bin/env python3
"""New, independent integer-interval attack on the fixed-degree disk integral.

All proof arithmetic uses outward rounding to 2^-72. Floats select where to
refine only. This is an experimental verifier; only completed reports count.
"""
from math import isqrt, log, comb
from fractions import Fraction as F
import heapq, itertools, json, argparse, time
from functools import lru_cache

BITS=72
S=1<<BITS

class I:
    __slots__=('lo','hi')
    def __init__(self,lo,hi=None,raw=False):
        if raw:self.lo,self.hi=lo,hi
        else:
            lo=F(lo); hi=lo if hi is None else F(hi)
            self.lo=lo.numerator*S//lo.denominator
            self.hi=-((-hi.numerator*S)//hi.denominator)
        assert self.lo<=self.hi
    def __add__(a,b):
        b=cv(b);return I(a.lo+b.lo,a.hi+b.hi,True)
    __radd__=__add__
    def __neg__(a):return I(-a.hi,-a.lo,True)
    def __sub__(a,b):return a+-cv(b)
    def __rsub__(a,b):return cv(b)+-a
    def __mul__(a,b):
        b=cv(b);v=(a.lo*b.lo,a.lo*b.hi,a.hi*b.lo,a.hi*b.hi)
        return I(min(v)//S,-((-max(v))//S),True)
    __rmul__=__mul__
    def __truediv__(a,b):
        b=cv(b);assert b.lo>0
        return a*I(S*S//b.hi,-((-S*S)//b.lo),True)
    def __rtruediv__(a,b):return cv(b)/a
    def sq(a):
        l=0 if a.lo<=0<=a.hi else min(a.lo*a.lo,a.hi*a.hi)
        h=max(a.lo*a.lo,a.hi*a.hi)
        return I(l//S,-((-h)//S),True)
    def sqrt(a):
        assert a.lo>=0
        l=isqrt(a.lo*S); h=isqrt(a.hi*S)
        return I(l,h+(h*h<a.hi*S),True)
    def mid(a):return I((a.lo+a.hi)//2,(a.lo+a.hi)//2,True)
    def __repr__(a):return str((float(F(a.lo,S)),float(F(a.hi,S))))

def cv(a):return a if isinstance(a,I) else I(a)

def log_scalar(a):
    assert a>0
    k=a.bit_length()-1-BITS
    # Exact power-of-two range reduction places x in [1,2).
    x=I(F(a,S*(1<<k)) if k>=0 else F(a*(1<<(-k)),S))
    u=(x-1)/(x+1); u2=u.sq(); t=u; total=I(0)
    for j in range(24):
        total=total+t/(2*j+1);t=t*u2
    # Positive atanh-series remainder, bounded for 0<=u<=1/3.
    out=2*total+I(0,F(9,4*49*3**49))
    return out+k*LN2

# Independent exact enclosure ln(2), atanh series with u=1/3.
_v=sum((F(2,(2*j+1)*3**(2*j+1)) for j in range(32)),F(0))
LN2=I(_v,_v+F(9,4*65*3**65))
def ilog(a):return I(log_scalar(a.lo).lo,log_scalar(a.hi).hi,True)

def arm(y,j):
    a=I(0);z=y.sq()
    for _ in range(1,j):a=z/(z+a)
    return a

def lam(y,d,a,b):
    P=y+a/y; Q=y+b/y; sy=P+Q
    M=(1+P*Q)/(sy-y)
    den=(4+y.sq())*(4+sy.sq())
    wr=(4+2*(P.sq()+Q.sq())+y*sy*(1+P*Q))/den
    wi=((2*P-y)*(1+Q.sq())+(2*Q-y)*(1+P.sq()))/den
    br=(2+y*M)/(4+y.sq()); bi=(2*M-y)/(4+y.sq())
    delta=(d-2)**2+d+y.sq()
    cr=(2-d)/delta; ci=-(2*y.sq()+d)/(2*y*delta)
    num=wr.sq()+wi.sq()-2*(cr*wr+ci*wi)+1/delta
    re=1/delta-cr*(br+wr)-ci*(bi+wi)+wr*br+wi*bi
    im=cr*(bi-wi)+ci*(wr-br)+wi*br-wr*bi
    denominator=(re.sq()+im.sq()).sqrt()+d/(2*y*delta)*((wr-br).sq()+(wi-bi).sq()).sqrt()
    value=num/denominator*(4+sy.sq()).sqrt()/(sy-y)
    return ilog(value)

def pa(*ps):
    o={}
    for p in ps:
        for e,c in p.items():o[e]=o.get(e,0)+c
    return {e:c for e,c in o.items() if c}
def pn(p):return {e:-c for e,c in p.items()}
def pm(p,q):
    o={}
    for e,c in p.items():
        for f,v in q.items():o[e+f]=o.get(e+f,0)+c*v
    return {e:c for e,c in o.items() if c}
def ps(p,k):return {e:k*c for e,c in p.items() if k*c}
def ca(z,w):return pa(z[0],w[0]),pa(z[1],w[1])
def cm(z,w):return pa(pm(z[0],w[0]),pn(pm(z[1],w[1]))),pa(pm(z[0],w[1]),pm(z[1],w[0]))
def cc(z):return z[0],pn(z[1])
def cn(z):return pa(pm(z[0],z[0]),pm(z[1],z[1]))
def cs(z,k):return ps(z[0],k),ps(z[1],k)
def cont(p):
    a,b={0:1},{1:1}
    for _ in range(1,p):a,b=b,pa(pm({1:1},b),a)
    return b,a

RADIX=256
def path_rho(p,slot):
    if p:return cont(p)
    # rho=y+a/y, a=(N5*D6+t)/(D5*D6), 0<=t<=1.
    n5={4:1,2:2};d5={4:1,2:3,0:1};d6={4:1,2:4,0:3}
    den=pm(d5,d6)
    num=pa(pm({2:1},den),pm(n5,d6),{RADIX**slot:1})
    return num,pm({1:1},den)

@lru_cache(None)
def image_polys(d,p,q):
    one={0:1};y={1:1}
    n1,d1=path_rho(p,1);n2,d2=path_rho(q,2)
    l=pm(d1,d2); s=pa(pm(n1,d2),pm(n2,d1));r=pm(n1,n2)
    A=(pa(r,pn(l)),pn(s));B=(pa(r,l),pa(pm(y,l),pn(s)))
    n0=(pa(ps(l,4),pn(pm(y,s))),pa(ps(s,2),ps(pm(y,l),2)))
    d0=(pa(pm(pm(y,y),l),pn(pm(y,s))),pa(ps(s,2),ps(pm(y,l),-2)))
    g=(ps(y,2*(2-d)),pa(ps(pm(y,y),2),{0:d}))
    Ng=ca(cm(A,g),cm(({1:2},{}),n0));Dg=ca(cm(B,g),cm(({1:2},{}),d0))
    den=pa(cn(Dg),ps(cn(B),-d*d))
    center=ca(cm(Ng,cc(Dg)),cs(cm(A,cc(B)),-d*d))
    det=ca(cm(A,d0),cs(cm(n0,B),-1))
    u=cn(center);v=ps(pm({2:1},cn(det)),4*d*d);w=pm(den,den)
    h=pa(u,v,pn(w))
    out=[u,v,w,h]
    common=min(e%RADIX for pol in out for e in pol)
    out=[{e-common:c for e,c in pol.items()} for pol in out]
    degree=max(e%RADIX for pol in out for e in pol)
    return out,degree

def pe(poly,x):
    v=I(0)
    for e in range(max(poly,default=0),-1,-1):v=v*x+poly.get(e,0)
    return v

@lru_cache(None)
def grouped_polys(d,p,q,inverse):
    polys,degree=image_polys(d,p,q)
    ans=[]
    for pol in polys:
        groups={}
        for e,c in pol.items():
            ey=e%RADIX;ea=(e//RADIX)%RADIX;eb=e//(RADIX**2)
            groups.setdefault(eb,{}).setdefault(ea,{})[degree-ey if inverse else ey]=c
        ans.append(groups)
    return ans

def eval_grouped(pol,x,a,b):
    out=I(0)
    for eb in range(max(pol),-1,-1):
        group=pol.get(eb,{})
        inner=I(0)
        for ea in range(max(group,default=0),-1,-1):inner=inner*a+pe(group.get(ea,{}),x)
        out=out*b+inner
    return out

def arm_box(y,p,t):
    if p:return arm(y,p)
    # The recurrence gives a6-a5 exactly 1/(D5 D6).
    z=y.sq();d5=z.sq()+3*z+1;d6=z.sq()+4*z+3
    return z*(z+2)/d5+t/(d5*d6)

def range_cell(left,right,d,p,q,a=I(0),b=I(0)):
    if left<F(1,4):
        y=I(left,right)
        return lam(y,d,arm_box(y,p,a),arm_box(y,q,b))
    inverse=left>=1
    x=I(1/right,1/left) if inverse else I(left,right)
    vals=[eval_grouped(pol,x,a,b) for pol in grouped_polys(d,p,q,inverse)]
    u,v,w,h=vals
    assert u.lo>=0 and v.lo>=0
    squared=1+(h-2*(u*v).sqrt())/w
    return ilog(squared)/2

def bern_arrays(left,right,d,p,q):
    inverse=left>=1;x=I(1/right,1/left) if inverse else I(left,right)
    arrays=[]
    for pol in grouped_polys(d,p,q,inverse):
        m=max(pol);n=max(max(g) for g in pol.values())
        power={(a,b):pe(poly,x) for b,g in pol.items() for a,poly in g.items()}
        arr=[]
        for i in range(n+1):
            row=[]
            for j in range(m+1):
                value=I(0)
                for (a,b),c in power.items():
                    if a<=i and b<=j:value=value+c*F(comb(i,a)*comb(j,b),comb(n,a)*comb(m,b))
                row.append(value)
            arr.append(row)
        arrays.append(arr)
    return arrays

def split_line(line):
    left=[line[0]];right=[line[-1]]
    while len(line)>1:
        line=[(a+b)/2 for a,b in zip(line,line[1:])]
        left.append(line[0]);right.append(line[-1])
    return left,list(reversed(right))

def split_arrays(arrays,axis):
    left=[];right=[]
    for arr in arrays:
        work=list(map(list,zip(*arr))) if axis==0 else arr
        pairs=[split_line(line) for line in work]
        a=[x[0] for x in pairs];b=[x[1] for x in pairs]
        if axis==0:a=list(map(list,zip(*a)));b=list(map(list,zip(*b)))
        left.append(a);right.append(b)
    return left,right

def array_ranges(arrays,midpoint=False):
    out=[]
    for arr in arrays:
        if midpoint:
            rows=[split_line(line)[0][-1] for line in arr]
            v=split_line(rows)[0][-1]
        else:v=I(min(c.lo for row in arr for c in row),max(c.hi for row in arr for c in row),True)
        out.append(v)
    u,v,w,h=out
    assert u.lo>=0 and v.lo>=0
    return ilog(1+(h-2*(u*v).sqrt())/w)/2

def bern_min_cell(left,right,d,p,q):
    arrays=bern_arrays(left,right,d,p,q)
    counter=itertools.count();heap=[];upper=None
    def push(arr,da,db):
        nonlocal upper
        mid=array_ranges(arr,True)
        upper=mid.hi if upper is None else min(upper,mid.hi)
        try:v=array_ranges(arr)
        except AssertionError:v=I(-1000000,1000000)
        heapq.heappush(heap,(v.lo,next(counter),arr,da,db))
        return mid.hi-mid.lo
    width=push(arrays,0,0);target=max(width*2,S//25 if not p and not q else S//100)
    iterations=0
    while upper-heap[0][0]>target:
        lo,_,arr,da,db=heapq.heappop(heap)
        if lo>=upper:continue
        axis=0 if not p and (q or da<=db) else 1
        a,b=split_arrays(arr,axis)
        da+=axis==0;db+=axis==1
        push(a,da,db);push(b,da,db)
        iterations+=1
        if iterations>512:raise AssertionError('refine ordinate first')
    return I(heap[0][0],upper,True)

def finite_cell(left,right,d,p,q):
    if p and q:return range_cell(left,right,d,p,q)
    if left>=F(1,4):return bern_min_cell(left,right,d,p,q)
    boxes=[(I(0,1) if not p else I(0),I(0,1) if not q else I(0))]
    counter=itertools.count();heap=[];upper=None
    def push(a,b):
        nonlocal upper
        # A fixed auxiliary midpoint gives a valid upper bound on the
        # pointwise minimum, uniformly throughout this ordinate interval.
        mid=range_cell(left,right,d,p,q,a.mid(),b.mid())
        upper=mid.hi if upper is None else min(upper,mid.hi)
        try:v=range_cell(left,right,d,p,q,a,b)
        except AssertionError:v=I(-1000000,1000000)
        heapq.heappush(heap,(v.lo,next(counter),a,b))
        return mid.hi-mid.lo
    width=push(*boxes[0])
    # Resolve arm uncertainty to below the ordinate uncertainty. The floor
    # prevents fruitless over-resolution as the ordinate interval shrinks.
    target=max(width*2,S//25 if not p and not q else S//100)
    iterations=0
    while upper-heap[0][0]>target:
        lo,_,a,b=heapq.heappop(heap)
        if lo>=upper:continue
        if a.hi-a.lo>=b.hi-b.lo:
            m=(a.lo+a.hi)//2
            push(I(a.lo,m,True),b);push(I(m,a.hi,True),b)
        else:
            m=(b.lo+b.hi)//2
            push(a,I(b.lo,m,True));push(a,I(m,b.hi,True))
        iterations+=1
        if iterations>512:raise AssertionError('refine ordinate first')
    return I(heap[0][0],upper,True)

def integrate(d,p,q,tol=F(1,250),limit=500000,start=F(1,65536)):
    # Origin and infinite-tail contributions are accounted for separately.
    start=F(start); end=F(8*d)
    edges=[start]
    while edges[-1]<end:edges.append(min(end,edges[-1]*F(5,4)))
    counter=itertools.count();heap=[];low=F(0);high=F(0);count=0
    def push(a,b):
        nonlocal low,high,count
        try:v=finite_cell(a,b,d,p,q)
        except AssertionError:
            m=(a+b)/2;push(a,m);push(m,b);return
        lo=(b-a)*F(v.lo,S);hi=(b-a)*F(v.hi,S)
        low+=lo;high+=hi;count+=1
        heapq.heappush(heap,(-float(hi-lo),next(counter),a,b,lo,hi))
    for a,b in zip(edges,edges[1:]):push(a,b)
    t=time.time()
    while high-low>tol:
        _,_,a,b,lo,hi=heapq.heappop(heap);low-=lo;high-=hi
        m=(a+b)/2;push(a,m);push(m,b)
        if count%10000<2:print('PROGRESS',d,p,q,count,float(low),float(high-low),round(time.time()-t,2),flush=True)
        if count>limit:raise RuntimeError(('cell limit',count,float(low),float(high-low)))
    return {'degree':d,'arms':[p,q],'finite_start':str(start),'finite_end':str(end),'finite_interval':[str(low),str(high)],'cells':len(heap),'evaluations':count,'finite_decimal':[float(low),float(high)],'status':'EXACT_FINITE_INTERVAL_ONLY'}

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('d',type=int);parser.add_argument('p',type=int);parser.add_argument('q',type=int);parser.add_argument('--tol',default='1/250')
    a=parser.parse_args();r=integrate(a.d,a.p,a.q,F(a.tol));print(json.dumps(r),flush=True)
