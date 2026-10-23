"""Restore a fully audited complete-scope capsule without relabelling prior proofs."""
import argparse,hashlib,io,json,pathlib,zipfile
from rg_github_artifacts import fetch_archive
ap=argparse.ArgumentParser();ap.add_argument('--manifest',type=pathlib.Path,required=True)
ap.add_argument('--build-directory',type=pathlib.Path,required=True)
ap.add_argument('--verified-local-archive',type=pathlib.Path);a=ap.parse_args()
m=json.loads(a.manifest.read_text());assert m['kind']=='INDEPENDENTLY_AUDITED_COMPLETE_SCOPE_CAPSULE'
assert m['mathlib']=='0df444a360eaa60ab8c11dca51a86af692955474' and m['lean_version']=='4.33.1'
data=a.verified_local_archive.read_bytes() if a.verified_local_archive else fetch_archive(m)
assert hashlib.sha256(data).hexdigest()==m['artifact_sha256']
build=a.build_directory.resolve();build.mkdir(parents=True,exist_ok=True)
with zipfile.ZipFile(io.BytesIO(data)) as z:
    assert len(z.namelist())==len(set(z.namelist()))
    capsule=json.loads(z.read('capsule.json'));assert capsule['kind']=='VERIFIED_COMPLETE_SCOPE_OBJECTS'
    receipt=json.loads(z.read('receipt.json'));assert receipt['modules']==m['modules']
    assert receipt['endpoints']==m['endpoints'] and receipt['mathlib']==m['mathlib']
    for n,row in m['modules'].items():
        assert n==row['module'] and n.startswith('Proofs.') and json.loads(z.read(n+'.json'))==row
        assert row['axiom_profiles'] and all(set(ax)<={'propext','Classical.choice','Quot.sound'} for ax in row['axiom_profiles'])
        obj=z.read(n.replace('.','/')+'.olean');assert hashlib.sha256(obj).hexdigest()==row['output_sha256']
        out=build/(n.replace('.','/')+'.olean');assert out.resolve().is_relative_to(build)
        out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(obj)
        if row['mode']=='PRIOR_VERIFIED_JOB_EXPORT':origin=row['origin']
        else:
            assert row['mode']=='FRESH_KERNEL_EXPORT'
            origin={k:m[k] for k in ['repository','run','job','source_commit','artifact_id','artifact_sha256']}
        restored={**row,'mode':'PRIOR_VERIFIED_JOB_EXPORT','origin':origin,
            'transport_capsule':{k:m[k] for k in ['run','job','source_commit','artifact_id','artifact_sha256']}}
        (build/(n+'.json')).write_text(json.dumps(restored,indent=2)+'\n')
print(json.dumps({'status':'RESTORED_AUDITED_COMPLETE_SCOPE_NOT_FRESH','modules':len(m['modules']),
    'original_prior_origins_preserved':True,'full_current_source_and_closure_recheck':'REQUIRED_BY_VERIFY_EXTENSION'}))
