"""Restore only source-bound exports proved in a named preceding Actions job.

This is explicit prior-job reuse, never a fresh replay. The next verifier still
recomputes each module's current source and complete dependency-closure hash.
"""
import argparse,hashlib,io,json,os,pathlib,urllib.error,urllib.parse,urllib.request,zipfile

ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--manifest',type=pathlib.Path,required=True)
ap.add_argument('--build-directory',type=pathlib.Path,required=True)
a=ap.parse_args()
m=json.loads(a.manifest.read_text())
assert m['mathlib']=='0df444a360eaa60ab8c11dca51a86af692955474'
assert m['lean_version']=='4.33.1'
allowed={'propext','Classical.choice','Quot.sound'}
token=os.environ['GITHUB_TOKEN']
api=f"https://api.github.com/repos/{m['repository']}/actions/artifacts/{m['artifact_id']}"
headers={'Authorization':'Bearer '+token,'Accept':'application/vnd.github+json','X-GitHub-Api-Version':'2022-11-28'}
def get(url):
 with urllib.request.urlopen(urllib.request.Request(url,headers=headers),timeout=120) as r:return r.read()
meta=json.loads(get(api))
assert not meta['expired'] and meta['digest']=='sha256:'+m['artifact_sha256']
assert meta['workflow_run']['id']==m['run'] and meta['workflow_run']['head_sha']==m['source_commit']
class NoRedirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,hdrs,newurl):return None
try:
 with urllib.request.build_opener(NoRedirect).open(urllib.request.Request(api+'/zip',headers=headers),timeout=120) as r:
  data=r.read()
except urllib.error.HTTPError as e:
 assert e.code in (301,302,303,307,308)
 destination=e.headers['Location']
 parsed=urllib.parse.urlparse(destination)
 assert parsed.scheme=='https' and parsed.hostname and not parsed.username and not parsed.password
 # The signed external download receives no GitHub authorization header.
 with urllib.request.urlopen(destination,timeout=120) as r:data=r.read()
assert hashlib.sha256(data).hexdigest()==m['artifact_sha256']
build=a.build_directory.resolve();build.mkdir(parents=True,exist_ok=True)
with zipfile.ZipFile(io.BytesIO(data)) as z:
 names=z.namelist();assert len(set(names))==len(names)
 for n,expected in m['modules'].items():
  assert n==expected['module'] and n.startswith('Proofs.')
  assert expected['mode']=='FRESH_KERNEL_EXPORT'
  assert expected['axiom_profiles'] and all(set(p)<=allowed for p in expected['axiom_profiles'])
  row=json.loads(z.read(n+'.json'));assert row==expected,n
  rel=n.replace('.','/')+'.olean';out=build/rel
  assert out.resolve().is_relative_to(build)
  obj=z.read(rel);assert hashlib.sha256(obj).hexdigest()==row['output_sha256'],n
  out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(obj)
  row=dict(row,mode='PRIOR_VERIFIED_JOB_EXPORT',origin=dict(repository=m['repository'],run=m['run'],job=m['job'],source_commit=m['source_commit'],artifact_id=m['artifact_id'],artifact_sha256=m['artifact_sha256']))
  (build/(n+'.json')).write_text(json.dumps(row,indent=2)+'\n')
print(json.dumps(dict(status='RESTORED_PRIOR_VERIFIED_EXPORTS_NOT_FRESH',modules=len(m['modules']),run=m['run'],job=m['job'],artifact_digest_verified=True,current_source_and_closure='MUST_BE_RECHECKED_BY_VERIFY_EXTENSION')))
