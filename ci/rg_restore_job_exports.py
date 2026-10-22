"""Restore only source-bound exports proved in a named preceding Actions job.

This is explicit prior-job reuse, never a fresh replay. The next verifier still
recomputes each module's current source and complete dependency-closure hash.
"""
import argparse,hashlib,io,json,os,pathlib,time,urllib.error,urllib.parse,urllib.request,zipfile

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
def api_open(url,opener=urllib.request.urlopen):
 started=time.monotonic()
 for attempt in range(4):
  try:return opener(urllib.request.Request(url,headers=headers),timeout=120)
  except urllib.error.HTTPError as error:
   if error.code in (301,302,303,307,308):raise
   body=error.read(4096).decode('utf-8',errors='replace')
   try:message=json.loads(body).get('message',body)
   except json.JSONDecodeError:message=body
   remaining=error.headers.get('x-ratelimit-remaining')
   reset=error.headers.get('x-ratelimit-reset')
   retry_after=error.headers.get('retry-after')
   print(json.dumps({'status':'GITHUB_ARTIFACT_API_ERROR','http_status':error.code,
     'rate_remaining':remaining,'rate_reset':reset,'retry_after':retry_after,
     'message':str(message)[:512],'attempt':attempt+1}),flush=True)
   delay=None
   if error.code in (403,429):
    if retry_after and retry_after.isdigit():delay=int(retry_after)+1
    elif remaining=='0' and reset and reset.isdigit():delay=max(1,int(reset)-int(time.time())+2)
    elif 'secondary rate limit' in str(message).lower():delay=60*(2**attempt)
   if delay is None or attempt==3 or time.monotonic()-started+delay>3700:raise
   deadline=time.monotonic()+delay
   while time.monotonic()<deadline:
    wait=min(30,deadline-time.monotonic())
    print(json.dumps({'status':'WAITING_FOR_DOCUMENTED_GITHUB_RATE_RESET',
      'remaining_seconds':round(deadline-time.monotonic()),'no_request_during_wait':True}),flush=True)
    time.sleep(wait)
 raise AssertionError('Unreachable API retry state')
def get(url):
 with api_open(url) as r:return r.read()
meta=json.loads(get(api))
assert not meta['expired'] and meta['digest']=='sha256:'+m['artifact_sha256']
assert meta['workflow_run']['id']==m['run'] and meta['workflow_run']['head_sha']==m['source_commit']
class NoRedirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,hdrs,newurl):return None
try:
 with api_open(api+'/zip',urllib.request.build_opener(NoRedirect).open) as r:
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
