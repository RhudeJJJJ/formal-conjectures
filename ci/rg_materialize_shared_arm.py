"""Materialize exactly one explicitly open arm chunk from pinned rational data.

This is an untrusted source producer, never a proof verifier. Lean separately
checks every polynomial identity, scalar table, sign, logarithm and cover.
"""
import argparse,hashlib,json,pathlib,shutil
from rg_shared_arm_common import module
from rg_shared_arm_source import body
R=pathlib.Path(__file__).resolve().parents[1];S=R/'Proofs/RG_Lean_20261019'
ap=argparse.ArgumentParser();ap.add_argument('--tag',choices=['30','00'],required=True)
ap.add_argument('--chunk',type=int,required=True);ap.add_argument('--plan-only',action='store_true');a=ap.parse_args()
plan=json.loads((R/'ci/rg_shared_arm_materialization_plan.json').read_bytes());p=plan['classes'][a.tag]
assert a.chunk in p['open_chunk_indices'], 'Refuse to alter an already checked chunk'
raw=(R/p['packet']).read_bytes();assert hashlib.sha256(raw).hexdigest()==p['packet_sha256']
for path,h in plan['producer_source_sha256'].items():assert hashlib.sha256((R/path).read_bytes()).hexdigest()==h,path
packet=json.loads(raw);leaves=[]
def walk(n):
    if n['kind'] in ['first','second']:walk(n['left']);walk(n['right'])
    else:assert n['kind']=='polynomial';leaves.append(n)
for c in packet['cells']:walk(c['tree'])
assert len(leaves)==p['leaf_count']
start=10*a.chunk;stop=min(start+10,len(leaves));assert start<stop
members=[]
for i in range(start,stop):
    imports,text=body(a.tag,i,leaves[i],shared_weights=True)
    data=module('DegreeOneLongClass'+a.tag,imports,text).encode()
    rel=f'Proofs/RadenkovicGutmanD1Long{a.tag}Leaf{i:05d}.lean'
    members.append((rel,data))
raw_need=sum(len(data) for _,data in members);free=shutil.disk_usage(S).free
assert free>raw_need+256*1024**2
report=dict(status='UNTRUSTED_GENERATED_SOURCES_PENDING_KERNEL',tag=a.tag,chunk=a.chunk,
 endpoint=f'Proofs.RadenkovicGutmanD1Long{a.tag}Chunk{a.chunk:03d}',packet_sha256=p['packet_sha256'],
 physical_leaf_indices=list(range(start,stop)),source_bytes=raw_need,
 members=[dict(path=rel,bytes=len(data),sha256=hashlib.sha256(data).hexdigest()) for rel,data in members],
 bounds_and_payments_changed=False,proven_chunks_changed=0,whole_class='OPEN')
dest=S/'build/generated_source_plans';dest.mkdir(parents=True,exist_ok=True)
(dest/f'{a.tag}_{a.chunk:03d}.json').write_text(json.dumps(report,indent=2)+'\n')
if not a.plan_only:
    for rel,data in members:
        target=S/rel;target.parent.mkdir(parents=True,exist_ok=True)
        pending=target.with_suffix('.lean.rg-pending');pending.write_bytes(data);pending.replace(target)
print(json.dumps({k:v for k,v in report.items() if k!='members'}))
