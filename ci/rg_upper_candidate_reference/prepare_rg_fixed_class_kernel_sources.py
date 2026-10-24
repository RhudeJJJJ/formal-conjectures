"""Write source-bound candidates for exact original fixed-degree class reserves."""
import argparse,hashlib,json,pathlib,re,shutil
from fractions import Fraction as Q
B=pathlib.Path(__file__).resolve().parents[2];R=B;P=R/'Proofs/RG_Lean_20261019/Proofs'
O=B/'work/rg_upper_candidates';O.mkdir(parents=True,exist_ok=True)
ap=argparse.ArgumentParser();ap.add_argument('--degree',type=int,required=True)
ap.add_argument('--p',type=int,required=True);ap.add_argument('--q',type=int,required=True)
ap.add_argument('--repair-cover-wrapper',action='store_true');ap.add_argument('--max-source-mib',type=int,default=8);a=ap.parse_args();assert 1<=a.max_source_mib<=64
assert 2<=a.degree<=45 and ((1<=a.p<=a.q<=4) or (1<=a.p<=4 and a.q==0) or (a.p==a.q==0))
d=json.loads((O/f'FIXED_DEGREE_{a.degree}_CLASS_{a.p}_{a.q}_CELLS_CANDIDATE.json').read_bytes())
report=d['report'];cells=d['cells'];assert all(c['kind']=='polynomial' for c in cells)
assert report['degree']==a.degree and report['physical_arms']==[a.p,a.q]
reserve=Q(report['normalized_original_reserve']);assert reserve==Q(2,report['original_cutoff'])
assert Q(report['finite_payment'])>reserve*Q(22,7)+Q(9,1000)+Q(1,2048)
c1,c2=report['class_indices'];prefix=f'FixedDegree{a.degree:02d}Class{a.p}{a.q}'
def q(x):
 x=Q(x);return str(x.numerator) if x.denominator==1 else f'({x.numerator}/{x.denominator})'
def head(ns,imports):
 return '/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/\n'+''.join('import '+m+'\n' for m in imports)+f'\nnamespace Gebendorfer.RadenkovicGutman.{ns}\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\nset_option backward.isDefEq.respectTransparency false\n'
sources=[];cellends=[]
for i,c in enumerate(cells):
 ns=prefix+f'Cell{i:03d}';t=head(ns,['Proofs.RadenkovicGutmanFastArmCoverIntegral'])
 t+='def cell : FastNestedCellData.Cell := {\n'
 for field,value in [('reciprocal',str(c['reciprocal']).lower()),('young',q(c['young'])),('squareLower',q(c['square_lower'])),('payment',q(c['payment'])),('logarithmK',str(c['logarithm_k'])),('logarithmN',str(c['logarithm_n'])),('poly',c['poly']),('affine',c['affine']),('degrees','!['+','.join(map(str,c['degrees']))+']'),('left','!['+','.join(map(q,c['box_left']))+']'),('width','!['+','.join(map(q,c['box_width']))+']')]:
  t+=f'  {field} := {value}\n'
 t+='}\n'
 t+=f'theorem checked : FastNestedCellData.accepts {a.degree} {c1} {c2} cell=true := by decide +kernel\n'
 t+=f'def slice : FastArmCoverIntegral.Slice := ⟨.leaf cell,{q(c["left"])},{q(c["right"])},cell.payment⟩\n'
 t+=f'theorem cover_checked : FastArmCover.accepts {a.degree} {c1} {c2} slice.lower slice.upper 0 1 0 1 slice.bound slice.cover=true := by\n'
 t+=f'  change decide (FastNestedCellData.accepts {a.degree} {c1} {c2} cell=true ∧ FastRectangularCell.shape cell {q(c["left"])} {q(c["right"])} 0 1 0 1=true ∧ cell.payment≤cell.payment)=true\n'
 t+='  rw [decide_eq_true_eq]\n  exact ⟨checked,by decide +kernel,le_rfl⟩\n'
 t+=f'theorem slice_checked : FastArmCoverIntegral.accepts {a.degree} {c1} {c2} slice=true :=\n  FastArmCoverIntegral.accepts_of_checks {a.degree} {c1} {c2} slice (by decide +kernel) (by decide +kernel) cover_checked\n'
 t+='#print axioms checked\n#print axioms cover_checked\n#print axioms slice_checked\n'
 t+=f'end Gebendorfer.RadenkovicGutman.{ns}\n'
 ep='Proofs.RadenkovicGutman'+ns;cellends.append(ep);sources.append((ep,t.encode()))
batches=[]
for bi,start in enumerate(range(0,len(cells),10)):
 es=cellends[start:start+10];ep='Proofs.RadenkovicGutman'+prefix+f'Batch{bi:03d}'
 t='/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/\n'+''.join('import '+e+'\n' for e in es)
 t+=''.join('#print axioms Gebendorfer.RadenkovicGutman.'+e.split('RadenkovicGutman')[1]+'.slice_checked\n' for e in es)
 sources.append((ep,t.encode()));batches.append(ep)
ns=prefix;t=head(ns,['Proofs.RadenkovicGutmanFixedClassKernelBase']+batches)
names=[prefix+f'Cell{i:03d}' for i in range(len(cells))]
t+='def partition : List FastArmCoverIntegral.Slice := ['+','.join(n+'.slice' for n in names)+']\n'
t+=f'def reserve : ℚ := {q(reserve)}\n'
t+=f'theorem all_checked : ∀ s∈partition, FastArmCoverIntegral.accepts {a.degree} {c1} {c2} s=true := by\n  simp only [partition,List.forall_mem_cons]\n  exact ⟨'+','.join(n+'.slice_checked' for n in names)+',fun _ h => False.elim (List.not_mem_nil h)⟩\n'
t+='theorem adjacent_checked : FixedClassChain.adjacent (1/1000) 1024 partition=true := by decide +kernel\n'
t+=f'theorem partition_checked : FastArmCoverIntegral.checkAt {a.degree} {c1} {c2} (1/1000) 1024 partition=true :=\n  FixedClassChain.check_of_adjacent {a.degree} {c1} {c2} (1/1000) 1024 partition adjacent_checked all_checked\n'
t+='theorem budget_checked : PaidFixedClassIntegral.accepts reserve (FastArmCoverIntegral.payment partition)=true := by decide +kernel\nopen scoped Classical\nnoncomputable section\n'
t+=f'theorem normalized_target {{V : Type*}} [Fintype V] [DecidableEq V]\n    (G : SimpleGraph V) (u : V) (p q : ℕ) (hd : G.degree u={a.degree})\n    (hp : ArmClasses.classify p={c1}) (hq : ArmClasses.classify q={c2}) :\n    (reserve : ℝ)<ActualFusionIntegral.normalizedIntegral G u p q 2 :=\n  PaidFixedClassIntegral.normalized_target G u p q {a.degree} (by decide) hd {c1} {c2} hp hq\n    reserve partition partition_checked budget_checked\nend\n'
t+='#print axioms all_checked\n#print axioms adjacent_checked\n#print axioms partition_checked\n#print axioms budget_checked\n#print axioms normalized_target\n'
t+=f'end Gebendorfer.RadenkovicGutman.{ns}\n';endpoint='Proofs.RadenkovicGutman'+ns;sources.append((endpoint,t.encode()))
raw=sum(len(b) for _,b in sources);free=shutil.disk_usage(B).free
assert raw<a.max_source_mib*1024**2 and free>8*1024**3+raw
plan={'status':'ORIGINAL_CLASS_CANDIDATE_SOURCES_REQUIRE_KERNEL','degree':a.degree,'class_indices':[c1,c2],
      'normalized_original_reserve':str(reserve),'cells':len(cells),'raw_bytes':raw,'free_bytes_before':free,
      'members':['Proofs/RG_Lean_20261019/'+ep.replace('.','/')+'.lean' for ep,_ in sources],
      'controls':[cellends[0],cellends[len(cellends)//2],cellends[-1]],'batches':batches,'endpoint':endpoint,
      'original_class':'OPEN','universal_rg':'OPEN','complete_submission':'NOT_SUBMITTED'}
(O/(prefix+'_SOURCE_PLAN.json')).write_text(json.dumps(plan,indent=2)+'\n')
for ep,blob in sources:
 p=P.parent/(ep.replace('.','/')+'.lean')
 if p.exists():
  before=p.read_bytes()
  if before!=blob:
   assert a.repair_cover_wrapper and 'Cell' in ep,p
   legacy=re.sub(r'  change decide \(FastNestedCellData\.accepts [^\n]*\)=true\n  rw \[decide_eq_true_eq\]\n',
     '  rw [FastArmCover.accepts,decide_eq_true_eq]\n',blob.decode()).encode()
   assert before==legacy,p
   p.write_bytes(blob)
 else:p.write_bytes(blob)
print(json.dumps({k:v for k,v in plan.items() if k not in ['members','batches']}))
