"""Transport a complete checked object scope while preserving every row's origin."""
import argparse,hashlib,json,pathlib,shutil
ap=argparse.ArgumentParser();ap.add_argument('--build-directory',type=pathlib.Path,required=True)
ap.add_argument('--output',type=pathlib.Path,required=True);a=ap.parse_args()
receipt=json.loads((a.build_directory/'receipt.json').read_text())
assert receipt['mathlib']=='0df444a360eaa60ab8c11dca51a86af692955474'
assert receipt['leancert']=='621a43d7cf21f87872392a01e874f2f1dbddc926'
assert 'version 4.33.1,' in receipt['lean'] and 0<len(receipt['modules'])<=512
raw=0;objects=[]
for n,row in receipt['modules'].items():
    assert n==row['module'] and n.startswith('Proofs.')
    assert row['axiom_profiles'] and all(set(ax)<={'propext','Classical.choice','Quot.sound'} for ax in row['axiom_profiles'])
    assert row['mode'] in ['FRESH_KERNEL_EXPORT','PRIOR_VERIFIED_JOB_EXPORT']
    if row['mode']=='PRIOR_VERIFIED_JOB_EXPORT':assert row['origin']['artifact_id'] and row['origin']['artifact_sha256']
    obj=a.build_directory/(n.replace('.','/')+'.olean');raw+=obj.stat().st_size
    with obj.open('rb') as f:assert hashlib.file_digest(f,'sha256').hexdigest()==row['output_sha256']
    assert json.loads((a.build_directory/(n+'.json')).read_text())==row
    objects.append((n,obj))
assert raw<=1024**3 and shutil.disk_usage(a.build_directory).free>=raw+256*1024**2
a.output.mkdir(parents=True,exist_ok=True)
for n,obj in objects:
    target=a.output/(n.replace('.','/')+'.olean');target.parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(obj,target);shutil.copyfile(a.build_directory/(n+'.json'),a.output/(n+'.json'))
    log=a.build_directory/(n+'.log')
    if log.exists():shutil.copyfile(log,a.output/log.name)
shutil.copyfile(a.build_directory/'receipt.json',a.output/'receipt.json')
report={'kind':'VERIFIED_COMPLETE_SCOPE_OBJECTS','modules':len(objects),'object_bytes':raw,
        'records_and_origins_unchanged':True,'fresh_kernel_exports':sum(r['mode']=='FRESH_KERNEL_EXPORT' for r in receipt['modules'].values()),
        'prior_exports_remain_prior':True,'whole_universal_RG':'OPEN'}
(a.output/'capsule.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
