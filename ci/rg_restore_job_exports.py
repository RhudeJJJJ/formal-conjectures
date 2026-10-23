"""Restore only source-bound exports proved in a named preceding Actions job.

This is explicit prior-job reuse, never a fresh replay. The next verifier still
recomputes each module's current source and complete dependency-closure hash.
"""
import argparse,hashlib,io,json,os,pathlib,time,urllib.error,urllib.parse,urllib.request,zipfile

ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--manifest',type=pathlib.Path,required=True)
ap.add_argument('--build-directory',type=pathlib.Path,required=True)
ap.add_argument('--verified-local-archive',type=pathlib.Path,
    help='Use an explicitly retained original ZIP only after matching its full original artifact digest')
a=ap.parse_args()
m=json.loads(a.manifest.read_text())
assert m['mathlib']=='0df444a360eaa60ab8c11dca51a86af692955474'
assert m['lean_version']=='4.33.1'
allowed={'propext','Classical.choice','Quot.sound'}
from rg_github_artifacts import fetch_archive
data=a.verified_local_archive.read_bytes() if a.verified_local_archive else fetch_archive(m)
assert hashlib.sha256(data).hexdigest()==m['artifact_sha256']
build=a.build_directory.resolve();build.mkdir(parents=True,exist_ok=True)
with zipfile.ZipFile(io.BytesIO(data)) as z:
 names=z.namelist();assert len(set(names))==len(names)
 if os.environ.get('RG_PROOFSTORE_HOST_PATH'):
  import shutil
  host=pathlib.Path(os.environ['RG_PROOFSTORE_HOST_PATH']).resolve()
  assert os.environ.get('GITHUB_ACTIONS')=='true' and os.environ.get('RUNNER_ENVIRONMENT')=='github-hosted'
  assert host==pathlib.Path(os.environ['GITHUB_WORKSPACE']).resolve() and build.is_relative_to(host)
  selected_bytes=sum(z.getinfo(n.replace('.','/')+'.olean').file_size for n in m['modules'])
  assert selected_bytes<=2*1024**3,'Compressed restore batch exceeds the explicit two GiB raw-write bound'
  assert shutil.disk_usage(host).free>=8*1024**3+2*selected_bytes,'Keep host reserve for both bounded restore workers'
  print(json.dumps(dict(status='OBSERVED_COMPRESSED_RESTORE_CAPACITY',selected_raw_object_bytes=selected_bytes,host_free_bytes=shutil.disk_usage(host).free,minimum_host_reserve_bytes=8*1024**3)),flush=True)
 for n,expected in m['modules'].items():
  assert n==expected['module'] and n.startswith('Proofs.')
  assert expected['mode']=='FRESH_KERNEL_EXPORT'
  assert expected['axiom_profiles'] and all(set(p)<=allowed for p in expected['axiom_profiles'])
  row=json.loads(z.read(n+'.json'));assert row==expected,n
  rel=n.replace('.','/')+'.olean';out=build/rel
  assert out.resolve().is_relative_to(build)
  obj=z.read(rel);assert hashlib.sha256(obj).hexdigest()==row['output_sha256'],n
  out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(obj)
  origin=dict(repository=m['repository'],run=m['run'],job=m['job'],source_commit=m['source_commit'],artifact_id=m['artifact_id'],artifact_sha256=m['artifact_sha256'])
  if 'origin_context' in m:origin['context']=m['origin_context']
  row=dict(row,mode='PRIOR_VERIFIED_JOB_EXPORT',origin=origin)
  (build/(n+'.json')).write_text(json.dumps(row,indent=2)+'\n')
print(json.dumps(dict(status='RESTORED_PRIOR_VERIFIED_EXPORTS_NOT_FRESH',modules=len(m['modules']),run=m['run'],job=m['job'],artifact_digest_verified=True,current_source_and_closure='MUST_BE_RECHECKED_BY_VERIFY_EXTENSION')))
