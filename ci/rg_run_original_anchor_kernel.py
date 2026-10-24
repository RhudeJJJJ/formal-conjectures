"""Reproduce one exact original middle anchor, retaining every source and witness."""
import argparse,hashlib,json,pathlib,re,shutil,subprocess,sys
R=pathlib.Path(__file__).resolve().parent.parent;S=R/'Proofs/RG_Lean_20261019';work=R/'work/rg_anchor_candidates'
ap=argparse.ArgumentParser();ap.add_argument('--endpoint',required=True);ap.add_argument('--use-retained-candidate',action='store_true');ap.add_argument('--bundle-directory',type=pathlib.Path);a=ap.parse_args()
match=re.fullmatch(r'Proofs\.RadenkovicGutmanWideAnchor(\d{3})OriginalAnchor',a.endpoint);assert match
index=int(match[1]);assert 5<=index<=679
manifest=json.loads((R/'ci/rg_middle_runtime_factory_sources.json').read_bytes())
assert manifest['ratio']=='1.2' and manifest['prefix']=='WideAnchor'
for row in manifest['sources']:assert hashlib.sha256((R/row['file']).read_bytes()).hexdigest()==row['sha256'],row['file']
assert shutil.disk_usage(R).free>8*1024**3+128*1024**2
work.mkdir(parents=True,exist_ok=True);ref=R/'ci/rg_anchor_candidate_reference';bundle=S/'build/fresh_exports/generated_source'
if a.bundle_directory:
    bundle=a.bundle_directory.resolve();assert bundle.is_relative_to((S/'build').resolve()) and not bundle.exists()
candidate=work/f'COMPACT_ORIGINAL_ANCHOR_{index:03d}_EPS28_RATIO_1_2_CANDIDATE.json'
commands=[]
if candidate.exists():assert a.use_retained_candidate,'Existing candidate must be explicitly selected'
else:commands.append(('prepare_rg_compact_anchor_candidates.py',['--anchor-index',str(index),'--ratio','1.2','--epsilon-power','28','--max-seconds','900','--max-cells','2048']))
commands += [
 ('prepare_rg_symbolic_anchor_sources.py',['--first',str(index),'--last',str(index),'--ratio','1.2','--prefix','WideAnchor']),
 ('prepare_rg_symbolic_original_anchor_assembly.py',['--anchor-index',str(index),'--ratio','1.2','--prefix','WideAnchor'])]
try:
    for name,args in commands:
        with (work/(f'ANCHOR{index:03d}_'+name+'.log')).open('wb') as stream:
            result=subprocess.run([sys.executable,'-B',str(ref/name),*args],cwd=R,stdout=stream,stderr=subprocess.STDOUT,timeout=1000)
        if result.returncode:
            print((work/(f'ANCHOR{index:03d}_'+name+'.log')).read_text(encoding='utf-8')[-24000:],flush=True)
            raise RuntimeError((name,result.returncode))
finally:
    bundle.mkdir(parents=True,exist_ok=True)
    for p in work.iterdir():
        if p.is_file() and (f'{index:03d}' in p.name):shutil.copyfile(p,bundle/p.name)
source_plan=json.loads((work/f'WIDEANCHOR_{index:03d}_{index:03d}_FILES.json').read_bytes())
assembly=json.loads((work/f'WIDEANCHOR{index:03d}_ASSEMBLY_FILES.json').read_bytes());members=source_plan+assembly
assert len(members)==len(set(members)) and 1<=len(members)<=512
base=json.loads((R/'ci/rg_reusable_analytic_kernel_base_complete_scope_capsule.json').read_bytes())['modules']
for path in json.loads((R/'ci/rg_symbolic_anchor005_control_prior_restore_plan.json').read_bytes()):
    for n,row in json.loads((R/path).read_bytes())['modules'].items():
        if n in base:assert base[n]['source_sha256']==row['source_sha256']
        base[n]=row
seen=set();fresh=[];raw_size=0;source_hashes={}
def visit(n):
    if n in seen:return
    seen.add(n);raw=(S/(n.replace('.','/')+'.lean')).read_bytes();digest=hashlib.sha256(raw).hexdigest()
    if n in base:assert digest==base[n]['source_sha256'],n
    else:fresh.append(n)
    for dep in re.findall(r'^import\s+(Proofs\.[\w.]+)',raw.decode(),re.M):visit(dep)
visit(a.endpoint)
assert set(fresh)=={'Proofs.'+pathlib.PurePosixPath(p).stem for p in members}
for rel in members:
    path=(R/rel).resolve();assert path.is_relative_to((S/'Proofs').resolve())
    raw=path.read_bytes();raw_size+=len(raw);assert raw_size<=64*1024**2
    target=bundle/rel;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(path,target)
    source_hashes[rel]=hashlib.sha256(raw).hexdigest()
(bundle/'generated_source_manifest.json').write_bytes((json.dumps(dict(endpoint=a.endpoint,anchor_index=index,ratio='1.2',source_sha256=source_hashes,kind='ORIGINAL_TARGET_REQUIRES_SUCCESSFUL_KERNEL_RECEIPT'),indent=2)+'\n').encode())
print(json.dumps(dict(status='COMPLETE_ORIGINAL_ANCHOR_PROOF_SOURCES_MATERIALIZED_REQUIRES_KERNEL',anchor=index,endpoint=a.endpoint,fresh=len(fresh),required=len(seen),raw_source_bytes=raw_size,both_arm_orders=True,mathematical_coverage_added=0)),flush=True)
