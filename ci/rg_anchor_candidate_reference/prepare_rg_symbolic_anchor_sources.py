"""Same original anchor witnesses; share source binding and use symbolic integer transforms."""
import argparse,hashlib,json,math,pathlib,shutil
from fractions import Fraction as Q
from rg_mean_polynomial_arithmetic import pack
B=pathlib.Path(__file__).resolve().parents[2];R=B;S=R/'Proofs/RG_Lean_20261019';O=B/'work/rg_anchor_candidates';O.mkdir(parents=True,exist_ok=True)
ap=argparse.ArgumentParser();ap.add_argument('--first',type=int,required=True);ap.add_argument('--last',type=int,required=True);ap.add_argument('--literal-data',action='store_true');ap.add_argument('--ratio',default='1.1');ap.add_argument('--prefix',default='');a=ap.parse_args()
assert 5<=a.first<=a.last<=679
assert Q(101,100)<=Q(a.ratio)<=Q(6,5)
assert not a.prefix or a.prefix.isalnum() and a.prefix[0].isupper()
assert a.ratio=='1.1' or a.prefix
assert shutil.disk_usage(B).free>8*1024**3+64*1024**2
files=[];controls=[];all_fresh=[];batches=[];reports=[]
original=(S/'Proofs/RadenkovicGutmanDegreeOneMiddleAnchorData.lean').read_bytes()
original_sha=hashlib.sha256(original).hexdigest()
import re
entries=re.findall(r'⟨(\d+),(\d+),(\d+),\((\d+)/(\d+)\)⟩',original.decode().split('def anchors : Array Anchor := #[',1)[1].split(']',1)[0])
assert len(entries)==680

def q(x):
    x=Q(x);return str(x.numerator) if x.denominator==1 else f'({x.numerator}/{x.denominator})'
def ints(xs):return '['+','.join(map(str,xs))+']'
def vec(ps):return '!['+','.join(ints(p) for p in ps)+']'
def ep(n):return 'Proofs.RadenkovicGutman'+n
def head(n,imports):return '/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/\n'+''.join('import '+x+'\n' for x in imports)+f'namespace Gebendorfer.RadenkovicGutman.{n}\nopen Set MeasureTheory\nopen scoped Classical\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\nset_option backward.isDefEq.respectTransparency false\n'
def put(n,t):
    raw=t.encode();path=S/(ep(n).replace('.','/')+'.lean')
    if path.exists():assert path.read_bytes()==raw,path
    else:path.write_bytes(raw)
    files.append('Proofs/RG_Lean_20261019/'+ep(n).replace('.','/')+'.lean');all_fresh.append(ep(n))

for index in range(a.first,a.last+1):
    cp=O/f"COMPACT_ORIGINAL_ANCHOR_{index:03d}_EPS28_RATIO_{a.ratio.replace('.','_')}_CANDIDATE.json";raw=cp.read_bytes();d=json.loads(raw);par=d['parameters']
    assert d['complete_interval_coverage'] and d['positive_exact_budget'] and par['anchor_index']==index
    nn,pp,qq,tn,td=map(int,entries[index])
    assert par['original_source_sha256']==original_sha and par['n']==nn
    assert par['recurrence_arms']==[pp,qq] and Q(par['original_target'])==Q(tn,td)
    assert Q(par['x'])==2-Q(2,nn) and par['epsilon']=='1/268435456' and 128<=Q(par['Y'])<=2048
    assert 1<=len(d['cells'])<=2048
    p,r=par['recurrence_arms'];x=Q(par['x']);data=pack(x,p,r);ps=[data[k] for k in ['us','vs','js','ns','sep']]
    D=math.lcm(*(Q(z).denominator for poly in ps for z in poly));M=max(map(len,ps))
    ip=[[int(Q(z)*D) for z in poly]+[0]*(M-len(poly)) for poly in ps]
    prefix=('Literal' if a.literal_data else '')+(a.prefix or 'SymbolicAnchor')+f'{index:03d}';source=prefix+'Source';names=[]
    t=head(source,['Proofs.RadenkovicGutmanIntegerPolynomialPaymentCell'])
    if a.literal_data:
        t+='deriving instance DecidableEq for ComputedGeneralPathData.Data\n'
        t+='def data : ComputedGeneralPathData.Data := {\n'
        for key,field in [('as_','a'),('bs','b'),('cs','c'),('es','e'),('us','U'),('vs','V'),('js','J'),('ns','N'),('sep','E')]:
            t+='  '+field+' := ['+','.join(map(q,data[key]))+']\n'
        t+='}\n'
        t+=f'theorem data_checked : data=ComputedGeneralPathData.build {q(x)} {p} {r} := by decide +kernel\n'
    else:t+=f'def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build {q(x)} {p} {r}\n'
    t+=f'def source : IntegerPolynomialPaymentCell.Source := {{den:={D},length:={M},poly:={vec(ip)}}}\n'
    t+='theorem source_checked : IntegerPolynomialPaymentCell.sourceChecks data source=true := by decide +kernel\n'
    t+=f'theorem path_checked : GeneralPathPolynomials.accepts {q(x)} {p} {r} data.a data.b data.c data.e=true := ComputedGeneralPathData.path_checked {q(x)} {p} {r}\n'
    t+=f'theorem path_swapped : GeneralPathPolynomials.accepts {q(x)} {r} {p} data.a data.b data.c data.e=true := ComputedGeneralPathData.path_swapped {q(x)} {p} {r}\n'
    t+=f'theorem norms_checked : RationalMobiusPolynomials.accepts data.a data.b data.c data.e data.U data.V data.J data.N data.E=true := ComputedGeneralPathData.norms_checked {q(x)} {p} {r}\n'
    if a.literal_data:
        for proof in ['path_checked','path_swapped','norms_checked']:
            begin=t.index('theorem '+proof+' :');end=t.index('\n',begin)
            line=t[begin:end]
            left,right=line.split(' := ',1)
            t=t[:begin]+left+' := by\n  rw [data_checked]\n  exact '+right+t[end:]
        t+='#print axioms data_checked\n'
    t+='#print axioms source_checked\n#print axioms path_checked\n#print axioms path_swapped\n#print axioms norms_checked\n'+f'end Gebendorfer.RadenkovicGutman.{source}\n';put(source,t)
    for i,w in enumerate(d['cells']):
        ns=prefix+f'Cell{i:03d}';names.append(ns);t=head(ns,[ep(source)])
        t+='def witness : ComputedPolynomialCell.Witness := {\n'
        for k in ['a','b','s','L','c','R','total','k','n','sFloor','nFloor','eFloor']:
            value='['+','.join(map(q,w[k]))+']' if k in ['s','L'] else q(w[k])
            t+=f'  {k} := {value}\n'
        t+='}\n'
        ds=math.lcm(*(Q(c).denominator for k in ['s','L'] for c in w[k]),Q(w['c']).denominator)
        left=Q(w['a']);width=Q(w['b'])-left;T=math.lcm(left.denominator,width.denominator);A=int(T*left);W=int(T*width)
        t+='noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {\n'
        t+=f' left:={A},width:={W},den:={T},localDen:={ds},lowerC:={int(ds*Q(w["c"]))},s:={ints(int(ds*Q(z)) for z in w["s"])},L:={ints(int(ds*Q(z)) for z in w["L"])},transformed:=fun i => IntegerPolynomialPaymentCell.affine ({source}.source.poly i) {A} {W} {T}\n}}\n'
        t+=f'theorem checked : IntegerPolynomialPaymentCell.checks {source}.source witness geometry=true := by\n  unfold IntegerPolynomialPaymentCell.checks\n  rw [decide_eq_true_eq]\n  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by intro i; rfl,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩\n'
        t+='theorem budget : SemanticPolynomialPaymentCell.Budget witness := by\n  unfold SemanticPolynomialPaymentCell.Budget\n  decide +kernel\n'
        t+='theorem logarithm_checked : RationalLog.accepts witness.c witness.R witness.k witness.n=true := by decide +kernel\nnoncomputable section\n'
        for swapped in [False,True]:
            pp,qq=(r,p) if swapped else (p,r);name='actual_integral_swapped' if swapped else 'actual_integral';hp='path_swapped' if swapped else 'path_checked'
            t+=f'theorem {name} {{V : Type*}} [Fintype V] [DecidableEq V]\n    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :\n    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),\n      MixedGraphIntegral.logarithm (CoreQuotient.source G u {pp} {qq}) (CoreQuotient.fused G u {pp} {qq}) (({q(x)} : ℚ) : ℝ) y :=\n  SemanticPolynomialPaymentCell.actual_integral_lower {q(x)} {pp} {qq} {source}.data\n    {source}.{hp} {source}.norms_checked witness\n    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry {source}.source_checked checked) budget logarithm_checked G u hd\n'
        t+='#print axioms checked\n#print axioms budget\n#print axioms logarithm_checked\n#print axioms actual_integral\n#print axioms actual_integral_swapped\nend\n'+f'end Gebendorfer.RadenkovicGutman.{ns}\n';put(ns,t)
    anchor_batches=[]
    for bi,start in enumerate(range(0,len(names),10)):
        ns=prefix+f'Batch{bi:03d}';ns_names=names[start:start+10]
        t='/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/\n'+''.join('import '+ep(n)+'\n' for n in ns_names)
        t+=''.join('#print axioms Gebendorfer.RadenkovicGutman.'+n+'.actual_integral\n' for n in ns_names)
        put(ns,t);anchor_batches.append(ep(ns));batches.append(ep(ns))
    controls.extend(ep(names[i]) for i in sorted(set([0,len(names)//2,len(names)-1])))
    reports.append(dict(anchor=index,original_candidate_sha256=hashlib.sha256(raw).hexdigest(),original_target=par['original_target'],source=ep(source),cells=len(names),batches=anchor_batches,
        original_quantifiers_unchanged=True,both_arm_orders=True,whole_anchor='OPEN',universal_rg='OPEN'))
tag=('LITERAL_' if a.literal_data else '')+(a.prefix.upper() if a.prefix else 'SYMBOLIC_ANCHORS')+f'_{a.first:03d}_{a.last:03d}'
for suffix,value in [('SOURCE_PLAN',reports),('FILES',files),('FRESH',all_fresh),('BATCH_ENDPOINTS',batches),('CONTROL_ENDPOINTS',controls)]:
    (O/(tag+'_'+suffix+'.json')).write_text(json.dumps(value,indent=2)+'\n')
control_fresh=[]
for report in reports:
    control_fresh.append(report['source'])
    control_fresh.extend(n for n in controls if n.startswith(report['source'].removesuffix('Source')+'Cell'))
(O/(tag+'_CONTROL_FRESH.json')).write_text(json.dumps(control_fresh,indent=2)+'\n')
print(json.dumps(dict(status='ORIGINAL_ANCHOR_SYMBOLIC_SOURCES_REQUIRE_KERNEL',anchors=len(reports),cells=sum(r['cells'] for r in reports),control_endpoints=len(controls),fresh_control_modules=len(control_fresh),raw_source_bytes=sum((R/p).stat().st_size for p in files),universal_rg='OPEN')))
