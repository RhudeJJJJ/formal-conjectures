"""Bound fresh original leaves and require exact historical source/output identity."""
import argparse,hashlib,json,pathlib,re,subprocess,sys
R=pathlib.Path(__file__).resolve().parents[1];S=R/'Proofs/RG_Lean_20261019'
sys.path.insert(0,str(S))
from verify import without_comments
from module_outputs import output_members
PIN='0df444a360eaa60ab8c11dca51a86af692955474'
LC='621a43d7cf21f87872392a01e874f2f1dbddc926'
ALLOWED={'propext','Classical.choice','Quot.sound'}
def digest(data):return hashlib.sha256(data).hexdigest()
def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--plan',type=pathlib.Path,required=True)
 ap.add_argument('--phase',choices=['source-plan','preflight','compare'],required=True)
 a=ap.parse_args();plan=json.loads(a.plan.read_bytes())
 assert plan['kind']=='EXACT_ORIGINAL_LEAF_REPRODUCTION' and plan['tag']=='00'
 chunk=plan['chunk'];assert isinstance(chunk,int) and 0<=chunk<=175
 ends=[f'Proofs.RadenkovicGutmanD1Long00Leaf{i:05d}' for i in range(10*chunk,min(10*chunk+10,1754))]
 assert plan['endpoints']==ends and 1<=len(ends)<=10
 assert plan['workers']==2 and plan['memory_reserve_mib']==2048 and plan['module_timeout']==1200
 manifests={}
 for key in ['original_manifest','base_manifest']:
  path=pathlib.Path(plan[key]);assert path.is_relative_to('ci') and '..' not in path.parts
  raw=(R/path).read_bytes();assert digest(raw)==plan[key+'_sha256'],path
  manifests[key]=json.loads(raw)
 original=manifests['original_manifest'];base=manifests['base_manifest']
 assert original['mathlib']==base['mathlib']==PIN
 assert original['lean_version']==base['lean_version']=='4.33.1'
 assert base['kind']=='INDEPENDENTLY_AUDITED_COMPLETE_SCOPE_CAPSULE'
 expected={n:original['modules'][n] for n in ends}
 build=S/'build/extension';out=S/'build/fresh_exports';out.mkdir(parents=True,exist_ok=True)
 sources=[]
 for n,row in expected.items():
  assert row['module']==n and row['mode']=='FRESH_KERNEL_EXPORT'
  assert row['axiom_profiles'] and all(set(p)<=ALLOWED for p in row['axiom_profiles'])
  raw=(S/(n.replace('.','/')+'.lean')).read_bytes();code=without_comments(raw.decode())
  assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\s',code,re.M),n
  deps=sorted(set(re.findall(r'^\s*(?:public\s+)?import\s+((?:Proofs|LeanCert)\.[\w.]+)\s*$',code,re.M)))
  source_hash=digest(raw)
  closure=digest(json.dumps([n,source_hash,PIN,LC,[(d,base['modules'][d]['source_closure_sha256']) for d in deps]],separators=(',',':')).encode())
  assert source_hash==row['source_sha256'] and closure==row['source_closure_sha256'],n
  sources.append(dict(module=n,source_sha256=source_hash,source_closure_sha256=closure))
 if a.phase=='source-plan':
  report=dict(status='EXACT_ORIGINAL_SOURCES_MATCH_NO_KERNEL_PROOF',endpoints=ends,modules=sources,
   original_run=original['run'],original_job=original['job'])
 elif a.phase=='preflight':
  frontiers=[]
  for n in ends:
   subprocess.run([sys.executable,'-B',str(R/'ci/rg_restore_with_kernel_fallback.py'),
    '--plan','ci/rg_empty_restore_plan.json','--build-directory',str(build),
    '--endpoint',n,'--max-fresh','1','--preflight-only'],cwd=R,check=True)
   frontier=json.loads((build/'bounded_kernel_fallback_plan.json').read_bytes())
   assert frontier['fresh_modules']==[n],frontier
   frontiers.append(frontier)
  report=dict(status='EXACT_ORIGINAL_LEAF_FRONTIER_NO_KERNEL_PROOF',endpoints=ends,frontiers=frontiers)
 else:
  receipt=json.loads((build/'receipt.json').read_bytes())
  assert receipt['scope']=='EXPLICIT_EXTENSION_CLOSURE'
  assert len(receipt['endpoints'])==len(ends) and set(receipt['endpoints'])==set(ends)
  assert receipt['mathlib']==PIN and receipt['leancert']==LC and 'version 4.33.1,' in receipt['lean']
  fresh={n:row for n,row in receipt['modules'].items() if row['mode']=='FRESH_KERNEL_EXPORT'}
  assert set(fresh)==set(ends),sorted(fresh)
  logical=0
  for n,row in fresh.items():
   old=expected[n];assert row==json.loads((build/(n+'.json')).read_bytes())
   for key in ['module','source_sha256','source_closure_sha256','output_sha256','axiom_profiles']:
    assert row[key]==old[key],(n,key)
   members=tuple(sorted(output_members(n,row)))
   assert members==tuple(sorted(output_members(n,old))),(n,'output member identity')
   for rel,sha,size in members:
    path=build/rel;assert path.resolve().is_relative_to(build.resolve())
    assert path.is_file() and (size is None or path.stat().st_size==size),(n,rel)
    with path.open('rb') as f:assert hashlib.file_digest(f,'sha256').hexdigest()==sha,(n,rel)
    logical+=path.stat().st_size
  report=dict(status='FRESH_KERNEL_OUTPUTS_MATCH_ORIGINAL_IDENTITY',endpoints=ends,
   required_modules=len(receipt['modules']),fresh_modules=len(fresh),verified_output_bytes=logical,
   original_run=original['run'],original_job=original['job'],
   original_source_commit=original['source_commit'],original_manifest_sha256=plan['original_manifest_sha256'])
 (out/('original_leaf_'+a.phase.replace('-','_')+'.json')).write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps({k:v for k,v in report.items() if k not in ['modules','frontiers']},separators=(',',':')),flush=True)
if __name__=='__main__':main()
