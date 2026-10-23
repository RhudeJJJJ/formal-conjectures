"""Restore proofs, then recompile a bounded exact frontier after transport errors.

This does not accept missing evidence as a proof. The mandatory subsequent Lean
verifier must freshly export every missing module and the complete endpoint.
Integrity failures and an excessive frontier remain hard failures.
"""
import argparse,hashlib,json,pathlib,re,subprocess,sys
R=pathlib.Path(__file__).resolve().parents[1];S=R/'Proofs/RG_Lean_20261019'
ap=argparse.ArgumentParser();ap.add_argument('--plan',type=pathlib.Path,required=True)
ap.add_argument('--build-directory',type=pathlib.Path,required=True);ap.add_argument('--endpoint',required=True)
ap.add_argument('--max-fresh',type=int,required=True);ap.add_argument('--workers',type=int,default=2)
ap.add_argument('--unavailable-artifacts',type=pathlib.Path)
ap.add_argument('--preflight-only',action='store_true');a=ap.parse_args()
assert 1<=a.max_fresh<=512 and 1<=a.workers<=2
build=a.build_directory.resolve();build.mkdir(parents=True,exist_ok=True)
if not a.preflight_only:
    unavailable=set(json.loads(a.unavailable_artifacts.read_bytes())) if a.unavailable_artifacts else set()
    groups={};original_paths=json.loads(a.plan.read_bytes())
    for p in original_paths:
        m=json.loads((R/p).read_bytes())
        if m['artifact_id'] in unavailable:continue
        g=groups.setdefault(m['artifact_id'],{**m,'modules':{}})
        assert all(g[k]==m[k] for k in ['repository','run','job','source_commit','artifact_id','artifact_sha256','lean_version','mathlib'])
        for n,row in m['modules'].items():
            assert n not in g['modules'] or g['modules'][n]==row,n
            g['modules'][n]=row
    directory=build/'grouped_restore_manifests';directory.mkdir(parents=True,exist_ok=True);grouped=[]
    for i,m in enumerate(sorted(groups.values(),key=lambda x:(-len(x['modules']),x['artifact_id']))):
        p=directory/f'{i:03d}.json';p.write_text(json.dumps(m,indent=2)+'\n');grouped.append(str(p))
    grouped_plan=directory/'plan.json';grouped_plan.write_text(json.dumps(grouped,indent=2)+'\n')
    print(json.dumps(dict(status='GROUPED_ORIGINAL_ARCHIVES_ONCE_PER_RUN',original_manifests=len(original_paths),original_archive_requests=len(grouped),known_unavailable_ids_skipped=sorted(unavailable))),flush=True)
    command=[sys.executable,'-B',str(R/'ci/rg_restore_plan_parallel.py'),'--plan',str(grouped_plan),'--build-directory',str(build),'--workers',str(a.workers)]
    proc=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    text=proc.stdout.decode('utf-8');(build/'prerequisite_restore_complete.log').write_bytes(proc.stdout)
    print(text,flush=True)
    if proc.returncode:
        # A hash/profile/manifest failure is never silently reclassified.
        assert 'AssertionError' not in text and 'IntegrityError' not in text,'Prior integrity failure'
        assert re.search(r'(?:HTTPError|URLError|TimeoutError|ConnectionError)',text),'Not a recognized transport failure'
sys.path.insert(0,str(S));from verify import without_comments
PIN='0df444a360eaa60ab8c11dca51a86af692955474';LC='621a43d7cf21f87872392a01e874f2f1dbddc926'
hashes={};deps={};closures={}
def visit(n):
    if n in hashes:return
    path=(S/'ThirdParty/LeanCert' if n.startswith('LeanCert.') else S)/(n.replace('.','/')+'.lean')
    raw=path.read_bytes();code=without_comments(raw.decode());hashes[n]=hashlib.sha256(raw).hexdigest()
    assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\s',code,re.M),n
    deps[n]=sorted(set(re.findall(r'^\s*(?:public\s+)?import\s+((?:Proofs|LeanCert)\.[\w.]+)\s*$',code,re.M)))
    for d in deps[n]:visit(d)
def closure(n):
    if n not in closures:closures[n]=hashlib.sha256(json.dumps([n,hashes[n],PIN,LC,[(d,closure(d)) for d in deps[n]]],separators=(',',':')).encode()).hexdigest()
    return closures[n]
visit(a.endpoint)
fresh=[];reused=[]
for n in sorted(deps):
    rp=build/(n+'.json');obj=build/(n.replace('.','/')+'.olean')
    if not rp.is_file() or not obj.is_file():fresh.append(n);continue
    row=json.loads(rp.read_bytes())
    assert row['module']==n and row['source_sha256']==hashes[n] and row['source_closure_sha256']==closure(n),n
    assert row['axiom_profiles'] and all(set(ax)<={'propext','Classical.choice','Quot.sound'} for ax in row['axiom_profiles']),n
    with obj.open('rb') as f:assert hashlib.file_digest(f,'sha256').hexdigest()==row['output_sha256'],n
    reused.append(n)
report=dict(status='EXACT_FRONTIER_REQUIRES_MANDATORY_FRESH_KERNEL_EXPORTS',endpoint=a.endpoint,
 required_modules=len(deps),verified_prior_objects=len(reused),fresh_modules=fresh,
 max_fresh=a.max_fresh,within_bound=len(fresh)<=a.max_fresh,proof_status='NOT_PROVEN_BY_RESTORE',complete_submission='NOT_SUBMITTED')
(build/'bounded_kernel_fallback_plan.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='fresh_modules'}),flush=True)
assert report['within_bound'],f'Exact fresh frontier {len(fresh)} exceeds authorized run bound {a.max_fresh}'
