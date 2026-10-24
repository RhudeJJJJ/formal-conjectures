"""Produce bounded exact candidates for one original fixed-degree class reserve.

The historical research source is imported read-only; all output stays here.
This creates certificate candidates, never a Lean completion claim.
"""
from fractions import Fraction as Q
from math import isqrt
import argparse,hashlib,heapq,itertools,json,pathlib,shutil,sys,time
import rg_nested_programs as npoly
B=pathlib.Path(__file__).resolve().parents[2];O=B/'work/rg_upper_candidates';O.mkdir(parents=True,exist_ok=True)
ap=argparse.ArgumentParser();ap.add_argument('--degree',type=int,required=True);ap.add_argument('--p',type=int,required=True);ap.add_argument('--q',type=int,required=True);ap.add_argument('--long-q',action='store_true');ap.add_argument('--long-both',action='store_true');ap.add_argument('--max-candidate-mib',type=int,default=20);args=ap.parse_args();assert 1<=args.max_candidate_mib<=128
assert (1<=args.p<=args.q<=4 and not args.long_q and not args.long_both) or (1<=args.p<=4 and args.q==0 and args.long_q and not args.long_both) or (args.p==args.q==0 and args.long_both and not args.long_q)
assert 2<=args.degree<=45
c1=4 if args.long_both else args.p-1;c2=4 if args.long_q or args.long_both else args.q-1
threshold_source=B/'Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanDegreeTwoThreeThresholds.lean'
threshold_bytes=threshold_source.read_bytes()
import re
if args.degree in [2,3]:
    line=next(l for l in threshold_bytes.decode().splitlines() if l.startswith(f'def threshold{args.degree} :'))
    table=[list(map(int,row.split(','))) for row in re.findall(r'!\[([0-9,]+)\]',line)]
    assert len(table)==5 and all(len(row)==5 for row in table)
    cutoff=table[c1][c2];reserve=Q(2,cutoff)
else:cutoff=13;reserve=Q(2,13)
SRC=B/'ci/rg_parameter_search_reference'
assert shutil.disk_usage(B).free>8*1024**3+20*1024**2
sources={n:hashlib.sha256((SRC/n).read_bytes()).hexdigest() for n in ['rg_tensor_transfer.py','rg_correlated_arm_transfer.py','rg_small_degree_interval_attack.py']}
sys.path.insert(0,str(SRC));import rg_tensor_transfer as t
I,S=t.I,t.S
def series(x,n=32):return sum((x**(2*i+1)/Q(2*i+1) for i in range(n)),Q(0))
def rational_log_payment(L):
    k=0
    while 2**k*L<1:k+=1
    v=2**k*L;u=(v-1)/(v+1)
    R=series(u)-k*(series(Q(1,3))+Q(1,3)**65/(1-Q(1,3)**2))
    return Q((R*S).numerator//(R*S).denominator,S),k
def candidate(arr,left,right):
    lo,hi=t.bounds(arr);kind='polynomial';L=None;young=None
    if lo<=-10**6*S:return lo,hi,dict(kind='unpaid',payment=str(Q(lo,S)))
    um,vm,jm=map(int,t.mids(arr));h=isqrt(vm*10**24//um);k=10**12
    assert h>0
    ratio=min(Q(int(j)*h*k,(h+k)*(h*int(u)+k*int(v))) for u,v,j in zip(*(x.flat for x in arr)))
    scaled=(ratio*S).numerator//(ratio*S).denominator;L=Q(scaled,S);assert L>0
    R,range_k=rational_log_payment(L);R=min(R,Q(lo,S));young=Q(h,k)
    return lo,hi,dict(kind=kind,payment=str(R),square_lower=str(L),young=str(young),logarithm_k=range_k,logarithm_n=32,reciprocal=left>=1)

start=Q(1,1000);end=Q(1024);target=reserve*Q(22,7)+Q(9,1000)+Q(1,2048)+Q(1,100000);origin_lo=Q(0)
edges=[start,Q(1,500),Q(1,200),Q(1,100),Q(1,50),Q(1,20),Q(1,10),Q(1,5),Q(1,2),Q(1),Q(2),Q(4),Q(8),Q(16),Q(32),Q(64),Q(128),Q(256),Q(512),Q(1024)]
heap=[];counter=itertools.count();total=Q(0);evaluations=0;started=time.monotonic()
def push(left,right,arr):
    global total,evaluations
    low,high,cert=candidate(arr,left,right);lower=(right-left)*Q(low,S);total+=lower;evaluations+=1
    score=(right-left)*max(Q(0),Q(high-low,S))
    heapq.heappush(heap,(-float(score),next(counter),left,right,arr,lower,cert))
for left,right in zip(edges,edges[1:]):push(left,right,t.initial(left,right,args.degree,args.p,args.q))
while total+origin_lo<=target or any(r[-1]['kind']=='unpaid' for r in heap):
    assert time.monotonic()-started<180,'BOUNDED_FIXED_CLASS_SEARCH_TIME_LIMIT'
    _,_,left,right,arr,lower,_=heapq.heappop(heap);total-=lower
    aa,bb=t.split(arr,0);mid=(left+right)/2
    if left>=1:mid=2*left*right/(left+right);aa,bb=bb,aa
    push(left,mid,aa);push(mid,right,bb)
    assert evaluations<=1400,'Bounded first-class prototype exceeded 1400 evaluations'
cells=[];poly_count=0;source_bytes=0
for _,_,left,right,arr,lower,cert in sorted(heap,key=lambda r:r[2]):
    row=dict(left=str(left),right=str(right),**cert)
    if cert['kind']=='polynomial':
        g=npoly.gap(args.degree,c1,c2,Q(cert['young']),Q(cert['square_lower']))
        p=g.reciprocal if cert['reciprocal'] else g.direct
        low=1/right if cert['reciprocal'] else left;wid=1/left-1/right if cert['reciprocal'] else right-left
        aff,deg=npoly.affine(p,[low,Q(0),Q(0)],[wid,Q(1),Q(1)])
        assert npoly.bernstein_nonnegative(aff,deg),(left,right)
        row.update(poly=npoly.lean(3,p),affine=npoly.lean(3,aff),degrees=deg,box_left=[str(low),'0','0'],box_width=[str(wid),'1','1'])
        source_bytes+=len(row['poly'])+len(row['affine']);poly_count+=1
    cells.append(row)
assert cells[0]['left']==str(start) and cells[-1]['right']==str(end)
assert all(a['right']==b['left'] for a,b in zip(cells,cells[1:]))
paid=sum(((Q(c['right'])-Q(c['left']))*Q(c['payment']) for c in cells),Q(0))
assert paid+origin_lo>target
report=dict(status='EXACT_CANDIDATE_CELLS_REQUIRE_LEAN_KERNEL_CHECKS',degree=args.degree,normalized_original_reserve=str(reserve),original_cutoff=cutoff,threshold_source_sha256=hashlib.sha256(threshold_bytes).hexdigest(),physical_arms=[args.p,args.q],class_indices=[c1,c2],start=str(start),end=str(end),cells=len(cells),polynomial_cells=poly_count,evaluations=evaluations,search_origin_adjustment=str(origin_lo),origin_reserve_in_final='-9/1000',finite_payment=str(paid),finite_search_payment=str(paid+origin_lo),target=str(target),source_references_read_only=sources,literal_polynomial_bytes=source_bytes,original_fixed_degree_class='OPEN',universal_RG_Lean='OPEN')
report.update(arm_class_labels=[args.p,args.q],physical_arm_classes=[str(v) if v else '>=5' for v in [args.p,args.q]],legacy_physical_arms_field_rule='Zero is the long-arm class label, meaning physical length at least five, not length zero')
payload=json.dumps(dict(report=report,cells=cells),indent=2)+'\n'
needed=len(payload.encode());report['candidate_bytes']=needed;report['candidate_limit_bytes']=args.max_candidate_mib*1024**2
if needed>=args.max_candidate_mib*1024**2:
    (O/f'FIXED_DEGREE_{args.degree}_CLASS_{args.p}_{args.q}_BUDGET_EXCEEDED.json').write_text(json.dumps(report,indent=2)+'\n')
    raise RuntimeError(f'CANDIDATE_RAW_BUDGET_EXCEEDED required={needed} limit={args.max_candidate_mib*1024**2}')
assert shutil.disk_usage(B).free>8*1024**3+needed
dest=O/f'FIXED_DEGREE_{args.degree}_CLASS_{args.p}_{args.q}_CELLS_CANDIDATE.json';assert not dest.exists();dest.write_bytes(payload.encode())
print(json.dumps(report))
