"""Retain the original anchor, quantifiers and both arm orders for every candidate."""
import argparse,hashlib,json,pathlib,re
from fractions import Fraction as Q
B=pathlib.Path(__file__).resolve().parents[2];R=B;P=R/'Proofs/RG_Lean_20261019/Proofs';O=B/'work/rg_anchor_candidates';O.mkdir(parents=True,exist_ok=True)
ap=argparse.ArgumentParser();ap.add_argument('--anchor-index',type=int,required=True);ap.add_argument('--ratio',default='1.1');ap.add_argument('--prefix',default='SymbolicAnchor');a=ap.parse_args();assert 5<=a.anchor_index<680
assert Q(101,100)<=Q(a.ratio)<=Q(6,5) and a.prefix.isalnum() and a.prefix[0].isupper()
d=json.loads((O/f"COMPACT_ORIGINAL_ANCHOR_{a.anchor_index:03d}_EPS28_RATIO_{a.ratio.replace('.','_')}_CANDIDATE.json").read_bytes());par=d['parameters']
raw=(P/'RadenkovicGutmanDegreeOneMiddleAnchorData.lean').read_bytes()
entries=re.findall(r'⟨(\d+),(\d+),(\d+),\((\d+)/(\d+)\)⟩',raw.decode().split('def anchors : Array Anchor := #[',1)[1].split(']',1)[0])
assert len(entries)==680 and hashlib.sha256(raw).hexdigest()==par['original_source_sha256']
n,p,q,tn,td=map(int,entries[a.anchor_index]);x=Q(2)-Q(2,n);prefix=a.prefix+f'{a.anchor_index:03d}'
assert par['n']==n and par['recurrence_arms']==[p,q] and Q(par['original_target'])==Q(tn,td) and Q(par['x'])==x
assert d['complete_interval_coverage'] and d['positive_exact_budget'] and par['epsilon']=='1/268435456'
assert 1<=len(d['cells'])<=2048 and 128<=Q(par['Y'])<=2048
def rat(value):
    f=Q(value);return str(f.numerator) if f.denominator==1 else f'({f.numerator}/{f.denominator})'
def put(text,name,value):
    text,count=re.subn(r'^def '+name+r' : ℚ := [^\n]*',lambda _:f'def {name} : ℚ := {rat(value)}',text,flags=re.M);assert count==1,name
    return text
def base(name):return (P/('RadenkovicGutmanCompactAnchor000'+name+'.lean')).read_text(encoding='utf-8').replace('CompactAnchor000',prefix).replace('51/26',rat(x)).replace('9 9',f'{p} {q}').replace('+9+9+2',f'+{p}+{q}+2')
def swapped(text,kind):
    start=text.index('theorem '+kind+' ');end=text.index('\nend\n',start);body=text[start:end].replace('theorem '+kind+' ','theorem '+kind+'_swapped ')
    body=body.replace(f'+{p}+{q}+2',f'+{q}+{p}+2').replace(f'(source G u {p} {q}) (fused G u {p} {q})',f'(source G u {q} {p}) (fused G u {q} {p})')
    if kind=='actual_bound':
        body=body.replace(f'normalizedIntegral G u {p} {q}',f'normalizedIntegral G u {q} {p}').replace(f'payment {p} {q}',f'payment {q} {p}').replace('.actual_integral G u','.actual_integral_swapped G u')
    elif 'computed_actual_integral' in body:body=body.replace('ComputedPositiveTail.computed_actual_integral (','ComputedPositiveTail.computed_actual_integral_swapped (')
    else:body=body.replace(f'logReciprocalB {p} {q}',f'logReciprocalB {q} {p}')
    return (text[:end]+'\n'+body+text[end:]).replace('#print axioms '+kind+'\n','#print axioms '+kind+'\n#print axioms '+kind+'_swapped\n')
sources=[]
t=base('Origin');t=re.sub(r'\b52\b',str(n),t)
for name,value in [('logEpsilon',d['origin_log_epsilon'][0]),('logReciprocalB',d['origin_log_reciprocal_B'][0]),('payment',d['origin_payment'])]:t=put(t,name,value)
ke,terms=d['origin_log_epsilon'][1:];kb,tb=d['origin_log_reciprocal_B'][1:];assert terms==tb==32
t=t.replace('28 32=true',f'{ke} 32=true').replace('12 32=true',f'{kb} 32=true').replace(f'{n} 28 12 32',f'{n} {ke} {kb} 32')
sources.append((prefix+'Origin',swapped(t,'actual_integral')))
t=base('PositiveTail')
for name,value in [('K',par['K']),('Y',par['Y']),('payment',d['tail_payment'])]:t=put(t,name,value)
sources.append((prefix+'PositiveTail',swapped(t,'actual_integral')))
count=len(d['cells']);names=[prefix+f'Cell{i:03d}' for i in range(count)];ns=prefix+'FinitePayment'
t='/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/\nimport Proofs.RadenkovicGutmanComputedIntegralAssembly\n'
t+=''.join(f'import Proofs.RadenkovicGutman{prefix}Batch{i:03d}\n' for i in range((count+9)//10))
t+=f'namespace Gebendorfer.RadenkovicGutman.{ns}\nopen Set MeasureTheory CoreQuotient\nopen scoped Classical\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\nset_option backward.isDefEq.respectTransparency false\n'
t+='def witnesses : List ComputedPolynomialCell.Witness := ['+','.join(v+'.witness' for v in names)+']\n'
t+='def payment : ℚ := '+rat(d['finite_payment'])+'\n'
t+=f'theorem chain_checked : RationalIntegralPartition.check (1/268435456) {rat(par["Y"])} (ComputedIntegralAssembly.slices witnesses)=true := by decide +kernel\n'
t+='theorem total_checked : RationalIntegralPartition.total (ComputedIntegralAssembly.slices witnesses)=payment := by decide +kernel\nnoncomputable section\n'
for swap in [False,True]:
    pp,qq=(q,p) if swap else (p,q);th='actual_integral_swapped' if swap else 'actual_integral'
    integrand=f'MixedGraphIntegral.logarithm (source G u {pp} {qq}) (fused G u {pp} {qq}) (({rat(x)} : ℚ) : ℝ)'
    t+=f'theorem {th} {{V : Type*}} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :\n    (payment : ℝ)≤∫ y : ℝ in ((1/268435456 : ℚ) : ℝ)..(({rat(par["Y"])} : ℚ) : ℝ), {integrand} y := by\n'
    t+=f'  have hw : ∀ w∈witnesses, (w.total : ℝ)≤∫ y : ℝ in (w.a : ℝ)..(w.b : ℝ), {integrand} y := by\n    simp only [witnesses,List.forall_mem_cons]\n    exact ⟨'+','.join(v+'.'+th+' G u hd' for v in names)+',fun _ h => False.elim (List.not_mem_nil h)⟩\n'
    t+=f'  have h : (RationalIntegralPartition.total (ComputedIntegralAssembly.slices witnesses) : ℝ)≤∫ y : ℝ in ((1/268435456 : ℚ) : ℝ)..(({rat(par["Y"])} : ℚ) : ℝ), {integrand} y := by\n'
    t+=f'    apply RationalIntegralPartition.integral_lower _ (ActualFusionIntegral.logarithm_integrable G u {pp} {qq} (({rat(x)} : ℚ) : ℝ)) (1/268435456) {rat(par["Y"])} (ComputedIntegralAssembly.slices witnesses) (by norm_num) chain_checked\n'
    t+='    intro z hz\n    obtain ⟨w,hm,rfl⟩ := List.mem_map.mp hz\n    exact hw w hm\n  rw [total_checked] at h\n  exact h\n'
t+='end\n#print axioms chain_checked\n#print axioms total_checked\n#print axioms actual_integral\n#print axioms actual_integral_swapped\n'+f'end Gebendorfer.RadenkovicGutman.{ns}\n';sources.append((ns,t))
t=base('OriginalAnchor').replace('anchors[0]?',f'anchors[{a.anchor_index}]?').replace(f'⟨52,9,9,target⟩',f'⟨{n},{p},{q},target⟩')
t=re.sub(r'\b52\b',str(n),t);t=re.sub(r'(?<![\w])128(?![\w])',rat(par['Y']),t);t=put(t,'target',par['original_target'])
sources.append((prefix+'OriginalAnchor',swapped(t,'actual_bound')))
files=[]
for name,text in sources:
    path=P/('RadenkovicGutman'+name+'.lean');blob=text.encode()
    if path.exists():assert path.read_bytes()==blob,path
    else:path.write_bytes(blob)
    files.append(path.relative_to(R).as_posix())
tag=(f'SYMBOLIC_ANCHOR{a.anchor_index:03d}' if a.prefix=='SymbolicAnchor' else a.prefix.upper()+f'{a.anchor_index:03d}')
for suffix,value in [('ASSEMBLY_FILES',files),('FINAL_ENDPOINTS',['Proofs.RadenkovicGutman'+prefix+'OriginalAnchor']),('FINAL_FRESH',['Proofs.RadenkovicGutman'+name for name,_ in sources])]:
    (O/(tag+'_'+suffix+'.json')).write_bytes((json.dumps(value,indent=2)+'\n').encode())
print(json.dumps(dict(status='SAME_ORIGINAL_ANCHOR_ASSEMBLY_REQUIRES_KERNEL',anchor=a.anchor_index,n=n,recurrence_arms=[p,q],target=par['original_target'],cells=count,both_arm_orders=True,universal_rg='OPEN',complete_submission='NOT_SUBMITTED')))
