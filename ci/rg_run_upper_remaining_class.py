"""Propose bounded data, then expose the exact original class to the Lean kernel."""
import argparse,hashlib,json,pathlib,re,shutil,subprocess,sys
R=pathlib.Path(__file__).resolve().parent.parent;S=R/'Proofs/RG_Lean_20261019'
ap=argparse.ArgumentParser();ap.add_argument('--endpoint',required=True);a=ap.parse_args()
match=re.fullmatch(r'Proofs\.RadenkovicGutmanFixedDegree(\d{2})Class([0-4])0',a.endpoint);assert match
degree,arm=map(int,match.groups());assert 5<=degree<=45
assert shutil.disk_usage(R).free>8*1024**3+256*1024**2
reference=R/'ci/rg_upper_candidate_reference';work=R/'work/rg_upper_candidates'
m=json.loads((R/'ci/rg_upper_remaining_source_manifest.json').read_bytes())
for row in m['sources']:
    assert hashlib.sha256((R/row['file']).read_bytes()).hexdigest()==row['sha256'],row['file']
work.mkdir(parents=True,exist_ok=True)
for name,arguments in [
    ('generate_rg_fixed_degree_class_candidates.py',['--degree',str(degree),'--p',str(arm),'--q','0','--max-candidate-mib','128','--long-both' if arm==0 else '--long-q']),
    ('prepare_rg_fixed_class_kernel_sources.py',['--degree',str(degree),'--p',str(arm),'--q','0','--max-source-mib','64'])]:
    with (work/(name+'.log')).open('wb') as stream:
        result=subprocess.run([sys.executable,'-B',str(reference/name),*arguments],cwd=R,stdout=stream,stderr=subprocess.STDOUT,timeout=1000)
    assert result.returncode==0,(name,result.returncode)
plan_path=work/f'FixedDegree{degree:02d}Class{arm}0_SOURCE_PLAN.json';plan=json.loads(plan_path.read_bytes())
assert plan['endpoint']==a.endpoint and plan['normalized_original_reserve']=='2/13'
assert 1<=len(plan['members'])<=512 and plan['raw_bytes']<64*1024**2
base=json.loads((R/'ci/rg_reusable_analytic_kernel_base_complete_scope_capsule.json').read_bytes())['modules']
seen=set();fresh=[]
def visit(n):
    if n in seen:return
    seen.add(n);raw=(S/(n.replace('.','/')+'.lean')).read_bytes()
    if n in base:assert hashlib.sha256(raw).hexdigest()==base[n]['source_sha256'],n
    else:fresh.append(n)
    for dep in re.findall(r'^import\s+(Proofs\.[\w.]+)',raw.decode(),re.M):visit(dep)
visit(a.endpoint)
assert len(fresh)==len(plan['members']) and len(fresh)<=512
bundle=S/'build/fresh_exports/generated_source';bundle.mkdir(parents=True,exist_ok=True)
source_hashes={}
for rel in plan['members']:
    path=(R/rel).resolve();assert path.is_relative_to(S.resolve())
    target=bundle/rel;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(path,target)
    source_hashes[rel]=hashlib.sha256(path.read_bytes()).hexdigest()
for path in work.iterdir():
    if path.is_file():shutil.copyfile(path,bundle/path.name)
(bundle/'generated_source_manifest.json').write_bytes((json.dumps(dict(endpoint=a.endpoint,source_sha256=source_hashes,kind='CANDIDATES_REQUIRE_SUCCESSFUL_KERNEL_RECEIPT'),indent=2)+'\n').encode())
print(json.dumps(dict(status='SAME_ORIGINAL_2_OVER_13_CLASS_MATERIALIZED_REQUIRES_KERNEL',endpoint=a.endpoint,degree=degree,classes=plan['class_indices'],required=len(seen),fresh=len(fresh),source_bytes=plan['raw_bytes'],mathematical_coverage_added=0)),flush=True)
