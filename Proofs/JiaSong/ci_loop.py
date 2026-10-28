# Bounded certificate-development driver. Publishes diagnostics only to its own fork log branch.
import hashlib,json,os,re,subprocess,tempfile,time,urllib.request
from pathlib import Path
repo='RhudeJJJJ/formal-conjectures'
branch='proof-jia-song-20261028'
logbranch='proof-jia-song-diagnostics-20261028'
token=os.environ.pop('PROOF_LOG_TOKEN')
original_event=os.environ['GITHUB_SHA']
run_id=os.environ['GITHUB_RUN_ID']
modules=["Bounds","Geometry","Spectrum","Full","ExactAudit"]
protected=['lean-toolchain','lake-manifest.json','FormalConjecturesUtil.lean','FormalConjectures/Paper/JiaSongRemoteness.lean']
def digest(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
pins={p:digest(p) for p in protected}
def api(method,path,data=None):
 req=urllib.request.Request('https://api.github.com/repos/'+repo+'/'+path,data=None if data is None else json.dumps(data).encode(),method=method,headers={'Authorization':'Bearer '+token,'Accept':'application/vnd.github+json','X-GitHub-Api-Version':'2022-11-28','Content-Type':'application/json'})
 with urllib.request.urlopen(req,timeout=30) as r:return json.load(r)
def publish(record):
 old=api('GET','git/ref/heads/'+logbranch)['object']['sha']
 tree=api('GET','git/commits/'+old)['tree']['sha']
 content=json.dumps(record,ensure_ascii=False,indent=2)
 tr=api('POST','git/trees',{'base_tree':tree,'tree':[{'path':'ProofDiagnostics/JiaSong/latest.json','mode':'100644','type':'blob','content':content}]})
 co=api('POST','git/commits',{'message':'Certificate diagnostics for '+record['source_sha'],'tree':tr['sha'],'parents':[old]})
 api('PATCH','git/refs/heads/'+logbranch,{'sha':co['sha'],'force':False})
 print('DIAGNOSTICS_COMMIT '+co['sha'],flush=True)
def git(*args):return subprocess.check_output(['git',*args],text=True).strip()
def refresh():
 subprocess.run(['git','fetch','--quiet','origin',branch],check=True)
 return git('rev-parse','FETCH_HEAD')
def check_axioms(log):
 rows=dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log))
 names=['JiaSong.full_conjecture3_8','JiaSong.Certificate.remoteness_value','JiaSong.Certificate.ordered_spectrum']
 allowed={'propext','Classical.choice','Quot.sound'}
 assert log.count('EXACT TYPE:')==1
 assert 'NEGATIVE CONTROL: changed proposition rejected' in log
 for n in names:assert n in rows and {s.strip() for s in rows[n].split(',')}<=allowed,(n,rows)
 assert 'sorryAx' in rows['JiaSong.conjecture3_8']
 return {n:rows[n] for n in names}
for cycle in range(1,13):
 head=refresh();subprocess.run(['git','reset','--hard',head],check=True)
 assert {p:digest(p) for p in protected}==pins,'Protected imported sources or shared helpers changed'
 record={'scope':'Exact original imported modules; actual checkout recorded separately from workflow event SHA','workflow_event_sha':original_event,'source_sha':head,'run_id':run_id,'cycle':cycle,'status':'failed','protected_hashes':pins,'proof_hashes':{n:digest('Proofs/JiaSong/'+n+'.lean') for n in modules},'results':[]}
 print('PROOF CHECKOUT SHA '+head,flush=True)
 jobs=[('statements',['lake','--wfail','build','FormalConjectures.Paper.JiaSongRemoteness'])]
 for folder,names in [('JiaSong',modules)]:
  Path('.lake/build/lib/lean/Proofs/'+folder).mkdir(parents=True,exist_ok=True)
  for n in names:jobs.append((n,['lake','env','lean','-DwarningAsError=true','-DautoImplicit=false','-DrelaxedAutoImplicit=false','-o',f'.lake/build/lib/lean/Proofs/{folder}/{n}.olean',f'Proofs/{folder}/{n}.lean']))
 for name,cmd in jobs:
  p=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=600)
  print('CHECKING '+name+' EXIT '+str(p.returncode),flush=True);print(p.stdout,flush=True)
  record['results'].append({'name':name,'exit_code':p.returncode,'output':p.stdout})
  if p.returncode:break
 if all(x['exit_code']==0 for x in record['results']):
  try:record['axioms']=check_axioms(record['results'][-1]['output']);record['status']='passed'
  except Exception as e:record['audit_error']=str(e)
 assert git('rev-parse','HEAD')==head
 publish(record)
 if record['status']=='passed':
  print('PASS: original full JiaSong Conjecture3.8, standard axioms only; admitted negative control rejected. SOURCE '+head,flush=True);raise SystemExit(0)
 if cycle==12:break
 print('WAITING up to600s for a repair on the same authorized proof branch',flush=True)
 deadline=time.monotonic()+600
 while time.monotonic()<deadline:
  time.sleep(10)
  if refresh()!=head:break
 else:
  print('No repair arrived in bounded interval; ending this development job.',flush=True);break
raise SystemExit(1)
