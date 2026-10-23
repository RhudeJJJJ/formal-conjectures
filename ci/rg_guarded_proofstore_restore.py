"""Restore one exact original scope with an observed host-space reserve."""
import argparse,hashlib,json,os,pathlib,shutil,subprocess,sys
ap=argparse.ArgumentParser();ap.add_argument('--manifest',required=True);ap.add_argument('--build-directory',required=True);a=ap.parse_args()
assert os.environ.get('GITHUB_ACTIONS')=='true' and os.environ.get('RUNNER_ENVIRONMENT')=='github-hosted'
workspace=pathlib.Path(os.environ['GITHUB_WORKSPACE']).resolve()
assert pathlib.Path(os.environ['RG_PROOFSTORE_HOST_PATH']).resolve()==workspace
build=pathlib.Path(a.build_directory).resolve();assert build==workspace/'Proofs/RG_Lean_20261019/build/extension'
manifest=json.loads(pathlib.Path(a.manifest).read_bytes())
assert 0<manifest['logical_member_bytes_upper_bound']<=2*1024**3
before=shutil.disk_usage(workspace).free;assert before>=10*1024**3,'Keep 8 GiB plus a bounded next archive/object write reserve'
subprocess.run([sys.executable,'-B','ci/rg_restore_job_exports.py','--manifest',a.manifest,'--build-directory',a.build_directory],check=True)
logical=0
for n,row in manifest['modules'].items():
    p=build/(n.replace('.','/')+'.olean')
    with p.open('rb') as stream:assert hashlib.file_digest(stream,'sha256').hexdigest()==row['output_sha256']
    logical+=p.stat().st_size
subprocess.run(['sync','-f',str(build)],check=True)
after=shutil.disk_usage(workspace).free;assert after>=8*1024**3
image=workspace/'rg-ephemeral-proofstore.btrfs'
report=dict(status='ORIGINAL_OBJECT_BYTES_RESTORED_AND_READ_BACK_THROUGH_COMPRESSION',manifest=a.manifest,
    objects=len(manifest['modules']),logical_object_bytes=logical,host_free_before=before,host_free_after=after,
    allocated_image_bytes=image.stat().st_blocks*512,logical_image_bytes=image.stat().st_size,
    new_kernel_compilations=0,universal_rg='OPEN')
dest=workspace/'rg-proofstore-roundtrip-reports';dest.mkdir(exist_ok=True)
(dest/(pathlib.Path(a.manifest).stem+'.json')).write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report),flush=True)
