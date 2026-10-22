"""Fetch a hash-bound original GitHub artifact; respect explicit rate-limit headers."""
import hashlib,json,os,time,urllib.error,urllib.parse,urllib.request

def fetch_archive(m):
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
    return data
