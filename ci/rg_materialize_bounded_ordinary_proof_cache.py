"""Keep every original proof byte; place a bounded hot set on ordinary storage.

Uncopied objects stay available through owned read-only symlinks. The following
strict verifier must recheck every source, closure and object hash before using
any prior object. This script proves no new mathematical statement.
"""
import argparse,hashlib,json,os,pathlib,re,shutil,sys,time
repo=pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0,str(repo/'Proofs/RG_Lean_20261019'))
from module_outputs import output_members
ap=argparse.ArgumentParser();ap.add_argument('--source-directory',type=pathlib.Path,required=True)
ap.add_argument('--target-directory',type=pathlib.Path,required=True)
ap.add_argument('--copy-budget-gib',type=int,default=32)
ap.add_argument('--minimum-host-reserve-gib',type=int,default=8);a=ap.parse_args()
assert os.environ.get('GITHUB_ACTIONS')=='true' and os.environ.get('RUNNER_ENVIRONMENT')=='github-hosted' and os.environ.get('RUNNER_OS')=='Linux'
assert 1<=a.copy_budget_gib<=32 and a.minimum_host_reserve_gib>=8
source_lexical=a.source_directory.absolute();source=source_lexical.resolve()
target=a.target_directory.absolute();assert not target.exists() and target.parent.resolve().is_relative_to(repo)
assert source.is_dir() and source_lexical==repo/'Proofs/RG_Lean_20261019/build/extension'
target.mkdir(parents=True);target=target.resolve()
assert target.is_relative_to(repo) and target.stat().st_dev==repo.stat().st_dev
assert source.stat().st_dev!=target.stat().st_dev,'The experiment requires a distinct ordinary target filesystem'
reserve=a.minimum_host_reserve_gib*1024**3;metadata_reserve=256*1024**2
free_before=shutil.disk_usage(repo).free
budget=min(a.copy_budget_gib*1024**3,free_before-reserve-metadata_reserve);assert budget>1024**3
records=[];names=set();objects=[]
for p in sorted(source.glob('*.json')):
 if not p.name.startswith(('Proofs.','LeanCert.')):continue
 raw=p.read_bytes();row=json.loads(raw);n=row['module']
 assert re.fullmatch(r'(?:Proofs|LeanCert)(?:\.[A-Za-z0-9_]+)+',n) and n not in names
 assert p.name==n+'.json' and row['mode']=='PRIOR_VERIFIED_JOB_EXPORT'
 assert row['axiom_profiles'] or n.startswith('LeanCert.')
 assert all(set(ax)<={'propext','Classical.choice','Quot.sound'} for ax in row['axiom_profiles'])
 names.add(n);records.append((p.name,raw));members=[]
 for rel,digest,expected_size in output_members(n,row):
  src=source/rel;size=src.stat().st_size
  assert src.resolve().is_relative_to(source) and (expected_size is None or size==expected_size)
  members.append((rel,src,size,digest))
 objects.append((sum(x[2] for x in members),n,members))
assert len(records)>=13000
objects.sort(key=lambda x:(x[0],x[1]))
plan=dict(status='BOUNDED_BYTE_IDENTICAL_LAYOUT_PLAN',modules=len(records),unique_logical_object_bytes=sum(x[0] for x in objects),
 copy_budget_bytes=budget,minimum_host_reserve_bytes=reserve,host_free_bytes_before=free_before,
 source_device=source.stat().st_dev,target_device=target.stat().st_dev,
 selection='Smallest complete module output sets first; preserve all others through symlinks',
 source_original_objects_preserved=True,mathematical_coverage_added=0)
(target/'ORDINARY_PROOF_CACHE_PLAN.json').write_text(json.dumps(plan,indent=2)+'\n')
print(json.dumps(plan),flush=True)
copied=linked=allocated=copy_modules=0;start=time.monotonic()
for i,(size,n,members) in enumerate(objects):
 do_copy=copied+size<=budget and shutil.disk_usage(repo).free>=reserve+metadata_reserve+size
 for rel,src,byte_count,expected in members:
  dest=target/rel;assert dest.resolve().is_relative_to(target) and not dest.exists()
  dest.parent.mkdir(parents=True,exist_ok=True)
  if do_copy:
   tmp=dest.with_name(dest.name+'.copying');assert not tmp.exists();h=hashlib.sha256()
   with src.open('rb') as inp,tmp.open('xb') as out:
    while chunk:=inp.read(4*1024**2):h.update(chunk);out.write(chunk)
    out.flush();os.fsync(out.fileno())
   assert h.hexdigest()==expected and tmp.stat().st_size==byte_count,rel
   tmp.replace(dest);copied+=byte_count;allocated+=dest.stat().st_blocks*512
  else:
   dest.symlink_to(src);linked+=byte_count
 if do_copy:copy_modules+=1
 if (i+1)%500==0:print(json.dumps(dict(status='ORDINARY_PROOF_CACHE_PROGRESS',modules=i+1,copied_bytes=copied,linked_bytes=linked)),flush=True)
for name,raw in records:(target/name).write_bytes(raw)
assert shutil.disk_usage(repo).free>=reserve
report=dict(plan,status='BYTE_IDENTICAL_ORDINARY_PROOF_CACHE_READY',copied_modules=copy_modules,
 copied_logical_bytes=copied,linked_logical_bytes=linked,copied_allocated_bytes=allocated,
 host_free_bytes_after=shutil.disk_usage(repo).free,seconds=round(time.monotonic()-start,3),
 mandatory_next_step='Strict source closure and object revalidation followed by the original full Lean main',
 universal_rg='OPEN',complete_submission='NOT_SUBMITTED')
(target/'ORDINARY_PROOF_CACHE_REPORT.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report),flush=True)
