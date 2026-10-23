"""Reserve space on a fresh hosted Linux runner without deleting proof inputs.

Only explicitly listed unused preinstalled SDKs may be removed. This program
refuses to run on a local machine or on a self-hosted runner.
"""
import argparse,json,os,pathlib,shutil,subprocess
ap=argparse.ArgumentParser();ap.add_argument('--required-free-gib',type=int,default=45);a=ap.parse_args()
assert os.environ.get('GITHUB_ACTIONS')=='true'
assert os.environ.get('RUNNER_ENVIRONMENT')=='github-hosted' and os.environ.get('RUNNER_OS')=='Linux'
workspace=pathlib.Path(os.environ['GITHUB_WORKSPACE']).resolve()
assert workspace.is_relative_to('/home/runner/work') and workspace.is_dir()
assert 32<=a.required_free_gib<=50
required=a.required_free_gib*1024**3
targets=[pathlib.Path(p) for p in ['/usr/local/lib/android','/usr/share/dotnet','/opt/ghc','/opt/hostedtoolcache/CodeQL']]
before=shutil.disk_usage(workspace).free;actions=[]
for p in targets:
    if shutil.disk_usage(workspace).free>=required:break
    if not p.exists():continue
    assert p.is_dir() and not p.is_symlink() and p.resolve()==p
    assert p not in workspace.parents and not p.is_relative_to(workspace)
    original=p.stat()
    allocated=int(subprocess.check_output(['sudo','du','-sB1',str(p)],text=True).split()[0])
    logical=int(subprocess.check_output(['sudo','du','-sb',str(p)],text=True).split()[0])
    assert allocated<64*1024**3 and logical<64*1024**3
    now=p.stat();assert (now.st_dev,now.st_ino)==(original.st_dev,original.st_ino) and p.resolve()==p
    free_before=shutil.disk_usage(workspace).free
    subprocess.run(['sudo','rm','-rf','--',str(p)],check=True)
    assert not p.exists()
    actions.append(dict(path=str(p),logical_bytes=logical,allocated_bytes=allocated,
        free_bytes_before=free_before,free_bytes_after=shutil.disk_usage(workspace).free))
report=dict(status='FRESH_HOSTED_RUNNER_STORAGE_RESERVATION',free_bytes_before=before,
 required_free_bytes=required,free_bytes_after=shutil.disk_usage(workspace).free,
 removed_unused_preinstalled_sdks=actions,proof_sources_and_exports_removed=0,local_machine_changes=0)
print(json.dumps(report),flush=True)
assert report['free_bytes_after']>=required,'Hosted runner still lacks the planned finite proof capacity'
