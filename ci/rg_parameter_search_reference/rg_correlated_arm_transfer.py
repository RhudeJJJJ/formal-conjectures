"""Exact polynomial identities for the entire long-arm recurrence box.

The executable tensor verifier imports only stable_polys.
"""
from fractions import Fraction as F
import rg_small_degree_interval_attack as a
I,S=a.I,a.S
from functools import lru_cache

@lru_cache(None)
def stable_polys(d,p,q,inv):
    # N=|Ng|^2-d^2|A|^2; U-V=E*N, so min|Q|=N/(sqrt(U)+sqrt(V)).
    pa,pm,pn,ps,cm,cn,ca=a.pa,a.pm,a.pn,a.ps,a.cm,a.cn,a.ca
    y={1:1};n1,d1=a.path_rho(p,1);n2,d2=a.path_rho(q,2)
    l=pm(d1,d2);s=pa(pm(n1,d2),pm(n2,d1));r=pm(n1,n2)
    aa=(pa(r,pn(l)),pn(s))
    n0=(pa(ps(l,4),pn(pm(y,s))),pa(ps(s,2),ps(pm(y,l),2)))
    g=(ps(y,2*(2-d)),pa(ps(pm(y,y),2),{0:d}))
    ng=ca(cm(aa,g),cm(({1:2},{}),n0))
    nn=pa(cn(ng),ps(cn(aa),-d*d));j=pm(nn,nn)
    (u,v,w,h),degree=a.image_polys(d,p,q)
    # Recover the common y power removed by image_polys from the degree.
    # Original U-V=E*N implies original V has known minimal y power.
    bb=(pa(r,l),pa(pm(y,l),pn(s)))
    d0=(pa(pm(pm(y,y),l),pn(pm(y,s))),pa(ps(s,2),ps(pm(y,l),-2)))
    det=ca(cm(aa,d0),a.cs(cm(n0,bb),-1))
    voriginal=ps(pm({2:1},cn(det)),4*d*d)
    shift=min(e%a.RADIX for e in voriginal)-min(e%a.RADIX for e in v)
    dg=ca(cm(bb,g),cm(({1:2},{}),d0))
    ee=pa(cn(dg),ps(cn(bb),-d*d))
    uoriginal={e+shift:v for e,v in u.items()}
    assert pa(uoriginal,pn(voriginal))==pm(ee,nn), 'U-V=E*N identity'
    assert min(e%a.RADIX for e in j)>=shift
    j={e-shift:c for e,c in j.items()}
    degree=max(e%a.RADIX for pol in (u,v,j) for e in pol)
    out=[]
    for pol in (u,v,j):
        groups={}
        for e,c in pol.items():
            ey=e%a.RADIX;ea=(e//a.RADIX)%a.RADIX;eb=e//a.RADIX**2
            groups.setdefault(eb,{}).setdefault(ea,{})[degree-ey if inv else ey]=c
        out.append(groups)
    return out

