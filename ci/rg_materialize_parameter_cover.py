"""Reproduce only the exact, source-hashed arm-cover leaves needed by a job."""
import argparse, hashlib, json, pathlib, re, shutil
from fractions import Fraction as Q
import rg_nested_programs as npoly

ap=argparse.ArgumentParser()
ap.add_argument('--packet',type=pathlib.Path,required=True)
ap.add_argument('--endpoint',required=True)
a=ap.parse_args()
root=pathlib.Path(__file__).resolve().parent.parent
src=root/'Proofs/RG_Lean_20261019'
assert a.packet.resolve().parent==root/'ci'
data=json.loads(a.packet.read_bytes())
assert data['kind']=='SOURCE_HASHED_EXACT_PARAMETER_COVER_RECIPES'
assert re.fullmatch(r'Proofs\.RadenkovicGutman\w+',a.endpoint)
assert shutil.disk_usage(src).free>8*1024**3
recipes=data['leaves'];seen=set();written=0

def q(x):
    x=Q(x)
    return str(x.numerator) if x.denominator==1 else f'({x.numerator}/{x.denominator})'

def materialize(n):
    global written
    c=recipes[n];ns=n.split('.')[-1].removeprefix('RadenkovicGutman')
    program=npoly.gap(data['degree'],*data['class_indices'],Q(c['young']),Q(c['square_lower']))
    p=program.reciprocal if c['reciprocal'] else program.direct
    aff,degree=npoly.affine(p,list(map(Q,c['box_left'])),list(map(Q,c['box_width'])))
    assert degree==c['degrees'] and npoly.bernstein_nonnegative(aff,degree),n
    t='/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/\nimport Proofs.RadenkovicGutmanFastArmCoverIntegral\n'
    t+=f'\nnamespace Gebendorfer.RadenkovicGutman.{ns}\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\nset_option backward.isDefEq.respectTransparency false\n'
    t+='def cell : FastNestedCellData.Cell := {\n'
    fields=[('reciprocal',str(c['reciprocal']).lower()),('young',q(c['young'])),('squareLower',q(c['square_lower'])),('payment',q(c['payment'])),('logarithmK',str(c['logarithm_k'])),('logarithmN',str(c['logarithm_n'])),('poly',npoly.lean(3,p)),('affine',npoly.lean(3,aff)),('degrees','!['+','.join(map(str,c['degrees']))+']'),('left','!['+','.join(map(q,c['box_left']))+']'),('width','!['+','.join(map(q,c['box_width']))+']')]
    for k,v in fields:t+=f'  {k} := {v}\n'
    d=data['degree'];c1,c2=data['class_indices']
    t+='}\n'+f'theorem checked : FastNestedCellData.accepts {d} {c1} {c2} cell=true := by decide +kernel\n#print axioms checked\n'
    t+=f'end Gebendorfer.RadenkovicGutman.{ns}\n'
    raw=t.encode();assert hashlib.sha256(raw).hexdigest()==c['source_sha256'],n
    path=src/(n.replace('.','/')+'.lean')
    if path.exists():assert path.read_bytes()==raw,n
    else:path.write_bytes(raw)
    written+=len(raw);assert written<=64*1024**2
    print(json.dumps({'status':'EXACT_LEAF_SOURCE_MATERIALIZED_REQUIRES_KERNEL','module':n,'bytes':len(raw),'source_sha256':c['source_sha256']}),flush=True)

def visit(n):
    if n in seen:return
    seen.add(n)
    if n in recipes:materialize(n)
    raw=(src/(n.replace('.','/')+'.lean')).read_text(encoding='utf-8')
    for dep in re.findall(r'^\s*import\s+(Proofs\.[\w.]+)\s*$',raw,re.M):visit(dep)

for n in data['control_endpoints']+[a.endpoint]:visit(n)
print(json.dumps({'status':'SELECTED_EXACT_SOURCES_READY_FOR_KERNEL_CHECK','modules':len(seen),'materialized_bytes':written,'mathematical_coverage_added':0}),flush=True)
