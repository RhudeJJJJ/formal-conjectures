"""Exact candidate covers of both arm parameters, retaining original reserves.

Each y interval receives the minimum of its parameter-leaf payments.  Parameter
volumes are never integrated or added to the y payment.
"""
from fractions import Fraction as Q
from math import isqrt
import argparse,hashlib,heapq,itertools,json,pathlib,shutil,sys,time,re
import rg_nested_programs as npoly
B=pathlib.Path(__file__).resolve().parent.parent;O=B/'work/rg_parameter_budget_search'
O.mkdir(parents=True,exist_ok=True)
ap=argparse.ArgumentParser();ap.add_argument('--degree',type=int,required=True)
ap.add_argument('--p',type=int,required=True);ap.add_argument('--core-depth',type=int,default=1)
ap.add_argument('--max-candidate-mib',type=int,default=128)
ap.add_argument('--max-evaluations',type=int,default=1400)
ap.add_argument('--max-search-seconds',type=int,default=180)
ap.add_argument('--search-only',action='store_true')
ap.add_argument('--run-label',default='')
ap.add_argument('--resume-grid',type=pathlib.Path)
ap.add_argument('--small-origin',action='store_true');a=ap.parse_args()
assert a.degree in [2,3] and a.p in [0,3] and a.core_depth in [1,2]
assert 1<=a.max_candidate_mib<=512
assert 19<=a.max_evaluations<=6000 and 1<=a.max_search_seconds<=10800
assert not a.run_label or re.fullmatch(r'[A-Z0-9_]{1,48}',a.run_label)
c1=4 if a.p==0 else 2;c2=4
threshold_path=B/'Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanDegreeTwoThreeThresholds.lean'
threshold_raw=threshold_path.read_bytes();line=next(x for x in threshold_raw.decode().splitlines() if x.startswith(f'def threshold{a.degree} :'))
table=[list(map(int,row.split(','))) for row in re.findall(r'!\[([0-9,]+)\]',line)]
reserve=Q(2,table[c1][c2]);assert shutil.disk_usage(B).free>8*1024**3+a.max_candidate_mib*1024**2
SRC=B/'ci/rg_parameter_search_reference'
sources={n:hashlib.sha256((SRC/n).read_bytes()).hexdigest() for n in ['rg_tensor_transfer.py','rg_correlated_arm_transfer.py','rg_small_degree_interval_attack.py']}
sys.path.insert(0,str(SRC));import rg_tensor_transfer as t
S=t.S
def series(x,n=32):return sum((x**(2*i+1)/Q(2*i+1) for i in range(n)),Q(0))
def log_payment(L):
    k=0
    while 2**k*L<1:k+=1
    v=2**k*L;z=(v-1)/(v+1)
    R=series(z)-k*(series(Q(1,3))+Q(1,3)**65/(1-Q(1,3)**2))
    return Q((R*S).numerator//(R*S).denominator,S),k
def leaf_candidate(arr,left,right,s0,s1,t0,t1):
    lo,hi=t.bounds(arr)
    if lo<=-10**6*S:return dict(kind='unpaid',payment=Q(lo,S),lo=lo,hi=hi,box=(s0,s1,t0,t1))
    um,vm,jm=map(int,t.mids(arr));h=isqrt(vm*10**24//um);k=10**12;assert h>0
    ratio=min(Q(int(j)*h*k,(h+k)*(h*int(u)+k*int(v))) for u,v,j in zip(*(x.flat for x in arr)))
    L=Q((ratio*S).numerator//(ratio*S).denominator,S);assert L>0
    R,rk=log_payment(L)
    return dict(kind='polynomial',payment=min(R,Q(lo,S)),lo=lo,hi=hi,
        square_lower=L,young=Q(h,k),logarithm_k=rk,logarithm_n=32,
        reciprocal=left>=1,box=(s0,s1,t0,t1))
axes=([1]*a.core_depth if c1==4 else [])+[2]*a.core_depth
def cover(arr,left,right,steps=axes,s0=Q(0),s1=Q(1),t0=Q(0),t1=Q(1)):
    if not steps:
        leaf=leaf_candidate(arr,left,right,s0,s1,t0,t1)
        return dict(kind='leaf',data=leaf),leaf['payment'],leaf['hi'],leaf['kind']=='unpaid'
    axis=steps[0];ll,rr=t.split(arr,axis)
    if axis==1:
        mid=(s0+s1)/2
        x=cover(ll,left,right,steps[1:],s0,mid,t0,t1);y=cover(rr,left,right,steps[1:],mid,s1,t0,t1)
    else:
        mid=(t0+t1)/2
        x=cover(ll,left,right,steps[1:],s0,s1,t0,mid);y=cover(rr,left,right,steps[1:],s0,s1,mid,t1)
    return dict(kind='first' if axis==1 else 'second',mid=mid,left=x[0],right=y[0]),min(x[1],y[1]),min(x[2],y[2]),x[3] or y[3]
start=Q(1,10000) if a.small_origin else Q(1,1000)
end=Q(1024)
pi_upper=Q(3927,1250) if a.small_origin else Q(22,7)
origin_cost=Q(3,2500) if a.small_origin else Q(9,1000)
target=reserve*pi_upper+origin_cost+Q(1,2048)+Q(1,100000)
edges=[start,Q(1,500),Q(1,200),Q(1,100),Q(1,50),Q(1,20),Q(1,10),Q(1,5),Q(1,2),Q(1),Q(2),Q(4),Q(8),Q(16),Q(32),Q(64),Q(128),Q(256),Q(512),end]
heap=[];counter=itertools.count();total=Q(0);evaluations=0;began=time.monotonic()
variant=('SMALL_ORIGIN_' if a.small_origin else '')+(a.run_label+'_' if a.run_label else '')
progress=O/f'{variant}PARAMETER_COVER_D{a.degree}_P{a.p}_DEPTH{a.core_depth}_SEARCH_PROGRESS.json'
def observe(status):
    value=dict(status=status,degree=a.degree,class_indices=[c1,c2],core_depth=a.core_depth,
        y_evaluations=evaluations,y_intervals=len(heap),payment=str(total),target=str(target),
        gap=str(total-target),unpaid_intervals=sum(x[-1] for x in heap),seconds=round(time.monotonic()-began,3),
        parameter_payment_rule='MINIMUM_OVER_THE_COMPLETE_COVER_NEVER_SUM',universal_rg='OPEN')
    value.update(start=str(start),end=str(end),interval_grid=[[str(x[2]),str(x[3])] for x in sorted(heap,key=lambda x:x[2])])
    payload=json.dumps(value,indent=2)+'\n';progress.write_text(payload)
    if status!='PARAMETER_COVER_SEARCH_OBSERVATION' or evaluations%500 in [0,1]:
        snapshot=progress.with_name(progress.stem+f'_EVAL{evaluations:05d}.json')
        if not snapshot.exists():snapshot.write_text(payload)
    print(json.dumps({k:v for k,v in value.items() if k!='interval_grid'}),flush=True)
def push(left,right,arr):
    global total,evaluations
    tree,R,hi,unpaid=cover(arr,left,right);paid=(right-left)*R;total+=paid;evaluations+=1
    score=(right-left)*max(Q(0),Q(hi,S)-R)
    heapq.heappush(heap,(-float(score),next(counter),left,right,arr,tree,paid,R,unpaid))
initial_intervals=list(zip(edges,edges[1:]))
if a.resume_grid:
    assert a.resume_grid.resolve().parent==O.resolve()
    previous=json.loads(a.resume_grid.read_bytes())
    assert previous['degree']==a.degree and previous['class_indices']==[c1,c2]
    assert Q(previous['start'])==start and Q(previous['end'])==end
    initial_intervals=[(Q(l),Q(r)) for l,r in previous['interval_grid']]
    assert initial_intervals and initial_intervals[0][0]==start and initial_intervals[-1][1]==end
    assert all(l<r for l,r in initial_intervals) and all(x[1]==y[0] for x,y in zip(initial_intervals,initial_intervals[1:]))
for l,r in initial_intervals:push(l,r,t.initial(l,r,a.degree,a.p,0))
observe('INITIAL_PARAMETER_COVER_SEARCH')
while total<=target or any(x[-1] for x in heap):
    if time.monotonic()-began>=a.max_search_seconds or evaluations>=a.max_evaluations:
        observe('BOUNDED_PARAMETER_COVER_SEARCH_OPEN');raise RuntimeError('Bounded parameter-cover search remains open')
    _,_,l,r,arr,_,paid,_,_=heapq.heappop(heap);total-=paid
    ll,rr=t.split(arr,0);mid=(l+r)/2
    if l>=1:mid=2*l*r/(l+r);ll,rr=rr,ll
    push(l,mid,ll);push(mid,r,rr)
    if evaluations%100 in [0,1]:observe('PARAMETER_COVER_SEARCH_OBSERVATION')
observe('PARAMETER_COVER_SEARCH_BUDGET_FOUND_REQUIRES_EXACT_CERTIFICATES')
if a.search_only:
    search_groups=[dict(left=str(l),right=str(r),bound=str(R),cover=tree)
        for _,_,l,r,_,tree,_,R,_ in sorted(heap,key=lambda x:x[2])]
    value=dict(status='BUDGET_SEARCH_ONLY_EXACT_POLYNOMIAL_CERTIFICATES_NOT_MATERIALIZED',
        degree=a.degree,physical_arms=[a.p,0],class_indices=[c1,c2],core_depth=a.core_depth,
        start=str(start),end=str(end),finite_payment=str(total),target=str(target),reserve=str(reserve),
        groups=search_groups,parameter_payment_rule='MINIMUM_OVER_COMPLETE_PARAMETER_COVER',
        historical_sources=sources,producer_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
        universal_rg='OPEN',complete_submission='NOT_SUBMITTED')
    dest=O/f'{variant}PARAMETER_SEARCH_ONLY_D{a.degree}_P{a.p}_DEPTH{a.core_depth}.json'
    assert not dest.exists();dest.write_text(json.dumps(value,default=str,indent=2)+'\n')
    print(json.dumps(dict(status=value['status'],groups=len(search_groups),file=dest.name)),flush=True)
    raise SystemExit(0)
leaves=[];groups=[]
def materialize(tree,l,r):
    if tree['kind']!='leaf':return dict(kind=tree['kind'],mid=str(tree['mid']),left=materialize(tree['left'],l,r),right=materialize(tree['right'],l,r))
    row=tree['data'];assert row['kind']=='polynomial'
    s0,s1,t0,t1=row['box'];g=npoly.gap(a.degree,c1,c2,row['young'],row['square_lower'])
    p=g.reciprocal if row['reciprocal'] else g.direct
    y=1/r if row['reciprocal'] else l;w=1/l-1/r if row['reciprocal'] else r-l
    aff,deg=npoly.affine(p,[y,s0,t0],[w,s1-s0,t1-t0]);assert npoly.bernstein_nonnegative(aff,deg),(l,r,row['box'])
    index=len(leaves)
    leaves.append(dict(kind='polynomial',left=str(l),right=str(r),payment=str(row['payment']),young=str(row['young']),
        square_lower=str(row['square_lower']),logarithm_k=row['logarithm_k'],logarithm_n=row['logarithm_n'],
        reciprocal=row['reciprocal'],parameter_box=list(map(str,row['box'])),poly=npoly.lean(3,p),affine=npoly.lean(3,aff),
        degrees=deg,box_left=list(map(str,[y,s0,t0])),box_width=list(map(str,[w,s1-s0,t1-t0]))))
    return dict(kind='leaf',index=index)
for _,_,l,r,_,tree,_,R,_ in sorted(heap,key=lambda x:x[2]):groups.append(dict(left=str(l),right=str(r),bound=str(R),cover=materialize(tree,l,r)))
assert groups[0]['left']==str(start) and groups[-1]['right']==str(end)
assert all(x['right']==y['left'] for x,y in zip(groups,groups[1:]))
paid=sum(((Q(x['right'])-Q(x['left']))*Q(x['bound']) for x in groups),Q(0));assert paid>target
report=dict(status='COMPLETE_PARAMETER_COVER_CANDIDATES_REQUIRE_KERNEL',degree=a.degree,physical_arms=[a.p,0],class_indices=[c1,c2],
    physical_arm_classes=['>=5' if a.p==0 else str(a.p),'>=5'],normalized_original_reserve=str(reserve),original_cutoff=table[c1][c2],
    threshold_source_sha256=hashlib.sha256(threshold_raw).hexdigest(),start=str(start),end=str(end),finite_payment=str(paid),target=str(target),
    y_intervals=len(groups),parameter_leaves=len(leaves),core_depth=a.core_depth,source_references_read_only=sources,
    integral_helper='PaidFixedClassSmallOriginIntegral' if a.small_origin else 'PaidFixedClassIntegral',
    pi_upper=str(pi_upper),origin_cost=str(origin_cost),
    parameter_payment_rule='MINIMUM_OVER_COMPLETE_PARAMETER_COVER',universal_rg='OPEN',complete_submission='NOT_SUBMITTED')
payload=(json.dumps(dict(report=report,leaves=leaves,groups=groups),indent=2)+'\n').encode()
assert len(payload)<a.max_candidate_mib*1024**2 and shutil.disk_usage(B).free>8*1024**3+len(payload)
dest=O/f'{variant}FIXED_DEGREE_{a.degree}_CLASS_{a.p}_0_PARAMETER_DEPTH{a.core_depth}_CANDIDATE.json';assert not dest.exists();dest.write_bytes(payload)
print(json.dumps(dict(**report,raw_bytes=len(payload))),flush=True)
