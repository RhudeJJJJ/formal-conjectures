"""Verify original successful proof exports and retain compact complete evidence.

This collector does not run Lean and does not create fresh proof records. It
checks the original archive/object bytes, source hashes and original job status.
"""
import argparse,hashlib,io,json,os,pathlib,re,urllib.error,urllib.parse,urllib.request,zipfile
ap=argparse.ArgumentParser();ap.add_argument('--plan',type=pathlib.Path,required=True);ap.add_argument('--output',type=pathlib.Path,required=True);a=ap.parse_args()
plan=json.loads(a.plan.read_text());out=a.output;out.mkdir(parents=True,exist_ok=True)
repo=plan['repository'];headers={'Authorization':'Bearer '+os.environ['GITHUB_TOKEN'],'Accept':'application/vnd.github+json','X-GitHub-Api-Version':'2022-11-28'}
def get(url):
    with urllib.request.urlopen(urllib.request.Request(url,headers=headers),timeout=120) as r:return r.read()
def digest(data):return hashlib.sha256(data).hexdigest()
def stream_digest(stream):
    h=hashlib.sha256()
    while data:=stream.read(1024**2):h.update(data)
    return h.hexdigest()
class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self,*args,**kwargs):return None
def redirected(url):
    try:
        with urllib.request.build_opener(NoRedirect).open(urllib.request.Request(url,headers=headers),timeout=120) as r:return r.read()
    except urllib.error.HTTPError as error:
        assert error.code in (301,302,303,307,308)
        target=error.headers['Location'];parts=urllib.parse.urlparse(target)
        assert parts.scheme=='https' and parts.hostname and not parts.username and not parts.password
        with urllib.request.urlopen(target,timeout=120) as r:return r.read()
reports=[];allowed={'propext','Classical.choice','Quot.sound'};source_root=pathlib.Path('Proofs/RG_Lean_20261019')
for item in plan['items']:
    prefix=item['prefix'];assert re.fullmatch('[a-z0-9_]+',prefix)
    original_job=json.loads(get(f'https://api.github.com/repos/{repo}/actions/jobs/{item["job"]}'))
    assert original_job['status']=='completed' and original_job['conclusion']=='success' and original_job['run_id']==item['run']
    assert original_job['head_sha']==item['source']
    meta=json.loads(get(f'https://api.github.com/repos/{repo}/actions/artifacts/{item["artifact"]}'))
    assert not meta['expired'] and meta['digest']=='sha256:'+item['archive_sha256']
    assert meta['workflow_run']['id']==item['run'] and meta['workflow_run']['head_sha']==item['source']
    archive=redirected(f'https://api.github.com/repos/{repo}/actions/artifacts/{item["artifact"]}/zip')
    assert len(archive)==meta['size_in_bytes'] and digest(archive)==item['archive_sha256']
    directory=out/prefix;directory.mkdir(exist_ok=True)
    with zipfile.ZipFile(io.BytesIO(archive)) as z:
        infos=z.infolist();assert len(set(z.namelist()))==len(infos)
        logical_bytes=sum(info.file_size for info in infos);assert logical_bytes<8*1024**3
        receipt_bytes=z.read('receipt.json');receipt=json.loads(receipt_bytes)
        assert receipt['endpoints']==[item['endpoint']]
        assert receipt['mathlib']=='0df444a360eaa60ab8c11dca51a86af692955474' and receipt['leancert']=='621a43d7cf21f87872392a01e874f2f1dbddc926'
        assert 'version 4.33.1,' in receipt['lean']
        fresh={n:row for n,row in receipt['modules'].items() if row['mode']=='FRESH_KERNEL_EXPORT'}
        for n,row in receipt['modules'].items():
            assert n==row['module'] and all(set(profile)<=allowed for profile in row['axiom_profiles'])
            path=(source_root/'ThirdParty/LeanCert' if n.startswith('LeanCert.') else source_root)/(n.replace('.','/')+'.lean')
            assert digest(path.read_bytes())==row['source_sha256'],n
        for n,row in fresh.items():
            assert json.loads(z.read(n+'.json'))==row
            with z.open(n.replace('.','/')+'.olean') as stream:assert stream_digest(stream)==row['output_sha256'],n
            log=z.read(n+'.log');assert b'sorryAx' not in log
            text=log.decode('utf-8')
            profiles=[sorted(set(x.strip() for x in entry.split(',') if x.strip())) for entry in re.findall(r'depends on axioms:\s*\[([^\]]*)\]',text)]
            profiles += [[] for _ in re.findall('does not depend on any axioms',text)]
            assert profiles==row['axiom_profiles'] and profiles,n
            assert not re.search(r'\b(error|warning)(?:\([^\n]*?\))?:',text),n
            (directory/(n+'.json')).write_bytes(z.read(n+'.json'))
            (directory/(n+'.log')).write_bytes(log)
        (directory/'receipt.json').write_bytes(receipt_bytes)
    original_log=redirected(f'https://api.github.com/repos/{repo}/actions/jobs/{item["job"]}/logs')
    (directory/'complete_job.log').write_bytes(original_log)
    report={**item,'status':'ORIGINAL_EXPORTS_VERIFIED_BY_CI_COLLECTOR','mathematical_recompilation':False,'proof_mode':'ORIGINAL_JOBS_FRESH_KERNEL_EXPORTS; NO_NEW_PROOF_RECORDS','archive_bytes':len(archive),'logical_member_bytes':logical_bytes,'fresh_objects_checked':len(fresh),'required_modules':len(receipt['modules']),'all_current_source_hashes_match':True,'all_standard_axioms':True,'full_original_job_log_sha256':digest(original_log),'receipt_sha256':digest(receipt_bytes),'binary_objects_retained':'ORIGINAL_BINARY_ARTIFACT; NOT_DUPLICATED_IN_EVIDENCE_PACKAGE'}
    (directory/'audit.json').write_text(json.dumps(report,indent=2)+'\n')
    reports.append(report);print(json.dumps({'verified':prefix,'fresh_objects':len(fresh),'archive_sha256':item['archive_sha256']}),flush=True)
(out/'collection.json').write_text(json.dumps({'status':'COMPLETE_VERIFIED_ORIGINAL_EVIDENCE','repository':repo,'reports':reports,'new_kernel_compilations':0},indent=2)+'\n')
