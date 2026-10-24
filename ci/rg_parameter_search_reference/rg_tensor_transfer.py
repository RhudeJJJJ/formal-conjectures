"""Exact integer tensor-Bernstein verification of all long-arm values.

Finite lower integrals only. Completing a run, not starting one, is a proof.
"""
import numpy as np
from fractions import Fraction as F
from math import comb,lcm,isqrt
import itertools,heapq,time,json,argparse
import rg_correlated_arm_transfer as c
import rg_small_degree_interval_attack as a
I,S=a.I,a.S

def initial(left,right,d,p,q):
    inv=left>=1
    lo,hi=(1/right,1/left) if inv else (left,right)
    polys=c.stable_polys(d,p,q,inv)
    degrees=[max(e for pol in polys for g in pol.values() for pp in g.values() for e in pp),
             max(aa for pol in polys for g in pol.values() for aa in g),
             max(b for pol in polys for b in pol)]
    restricted=[]
    for pol in polys:
        pp={}
        for b,g in pol.items():
            for aa,univ in g.items():
                for e,v in univ.items():
                    for k in range(e+1):
                        key=(k,aa,b)
                        pp[key]=pp.get(key,F(0))+v*comb(e,k)*lo**(e-k)*(hi-lo)**k
        restricted.append(pp)
    scale=lcm(*(v.denominator for pol in restricted for v in pol.values()))
    out=np.zeros((3,)+tuple(n+1 for n in degrees),dtype=object)
    for i,pol in enumerate(restricted):
        for e,v in pol.items():out[(i,)+e]=v.numerator*(scale//v.denominator)
    for axis,n in enumerate(degrees,1):
        factor=lcm(*(comb(n,k) for k in range(n+1)))
        matrix=np.array([[comb(j,k)*(factor//comb(n,k)) if k<=j else 0 for k in range(n+1)] for j in range(n+1)],dtype=object)
        out=np.moveaxis(np.tensordot(matrix,out,axes=(1,axis)),0,axis)
    return out

def split(arr,axis):
    work=np.moveaxis(arr,axis+1,0);n=len(work)-1
    left=np.empty_like(work);right=np.empty_like(work);temp=work.copy()
    left[0]=temp[0]*(1<<n);right[n]=temp[-1]*(1<<n)
    for level in range(1,n+1):
        temp=temp[:-1]+temp[1:];factor=1<<(n-level)
        left[level]=temp[0]*factor;right[n-level]=temp[-1]*factor
    return np.moveaxis(left,0,axis+1),np.moveaxis(right,0,axis+1)

def mids(arr):
    out=arr
    for n in arr.shape[:0:-1]:
        weights=np.array([comb(n-1,k) for k in range(n)],dtype=object)
        out=np.tensordot(out,weights,axes=(-1,0))
    return out

def bounds(arr):
    u,v,j=map(int,mids(arr));assert u>0 and v>0 and j>0
    upper=(a.ilog(I(F(j,u))/(1+I(F(v,u)).sqrt()).sq())/2).hi
    h=isqrt(v*10**24//u);k=10**12
    assert h>0
    ur,vr,jr=[x.flat for x in arr]
    lower=None
    for ui,vi,ji in zip(ur,vr,jr):
        denom=(h+k)*(h*ui+k*vi)
        if denom<=0 or ji<=0:return -10**6*S,upper
        val=(ji*h*k*S)//denom
        lower=val if lower is None else min(lower,val)
    if lower<=0:return -10**6*S,upper
    return a.ilog(I(lower,lower,True)).lo//2,upper

def cell(arr,p,q,budget=16):
    heap=[];counter=itertools.count();upper=None
    def push(arr,da,db):
        nonlocal upper
        lo,hi=bounds(arr);upper=hi if upper is None else min(upper,hi)
        heapq.heappush(heap,(lo,next(counter),arr,da,db))
    push(arr,0,0)
    for _ in range(budget):
        if upper-heap[0][0]<S//2000:break
        lo,_,aa,da,db=heapq.heappop(heap)
        if lo>=upper:return upper,upper
        axis=1 if not p and (q or da<=db) else 2
        l,r=split(aa,axis);da+=axis==1;db+=axis==2
        push(l,da,db);push(r,da,db)
    return min(heap[0][0],upper),upper

def integrate(d,p,q,target=F(1,4),limit=10000):
    start=F(1,1000);end=F(8*d)
    # The separate origin proof gives log(2*y/7) for all y<=1.
    origin=I(start)*(a.ilog(I(2*start/F(7)))-1)
    origin_lo=F(origin.lo,S)
    edges=[start,F(1,500),F(1,200),F(1,100),F(1,50),F(1,20),F(1,10),F(1,5),F(1,2),F(1),F(2),F(4),F(8),end]
    heap=[];counter=itertools.count();total=F(0);count=0
    t=time.time()
    def push(left,right,arr):
        nonlocal total,count
        low,high=cell(arr,p,q)
        if right<=1:
            low=max(low,a.ilog(I(2*left/F(7))).lo)
        else:low=max(low,I(-1/(2*left*left)).lo)
        lower=(right-left)*F(low,S)
        total+=lower;count+=1
        score=(right-left)*max(0,F(high-low,S))
        heapq.heappush(heap,(-float(score),next(counter),left,right,arr,lower))
    for left,right in zip(edges,edges[1:]):
        push(left,right,initial(left,right,d,p,q))
    while total+origin_lo<=target:
        _,_,left,right,arr,lower=heapq.heappop(heap);total-=lower
        m=(left+right)/2
        # Bernstein ordinate is inverse y above 1, so the midpoint in u
        # corresponds to the harmonic midpoint in y, with reversed order.
        aa,bb=split(arr,0)
        if left>=1:
            m=2*left*right/(left+right);aa,bb=bb,aa
        push(left,m,aa);push(m,right,bb)
        if count%100<2:print('PROGRESS',d,p,q,count,float(total+origin_lo),round(time.time()-t,1),flush=True)
        if count>=limit:raise RuntimeError(('LIMIT',count,float(total+origin_lo)))
    return {'status':'EXACT_FINITE_PLUS_ORIGIN_LOWER','degree':d,'arms':[p,q],
            'long_arm_semantics':'0 denotes all p>=5 via a5+t/(D5*D6), 0<=t<=1',
            'start':str(start),'end':str(end),'target':str(target),
            'origin_lower':str(origin_lo),'finite_lower':str(total),
            'combined_lower':str(total+origin_lo),'cells':len(heap),'evaluations':count}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('d',type=int);p.add_argument('p',type=int);p.add_argument('q',type=int);p.add_argument('--target',default='1/4')
    args=p.parse_args();r=integrate(args.d,args.p,args.q,F(args.target))
    name=f'rg_long_transfer_{args.d}_{args.p}_{args.q}.json'
    open(name,'w').write(json.dumps(r,indent=2)+'\n');print(r,flush=True)
