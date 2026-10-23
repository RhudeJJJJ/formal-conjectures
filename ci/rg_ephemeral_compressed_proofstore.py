"""Transparent byte-preserving storage, only on a fresh GitHub-hosted runner.

The sparse image is a new temporary CI object. No existing disk is formatted.
Space success is measured, not inferred from an expected compression ratio.
"""
import argparse,hashlib,json,os,pathlib,shutil,subprocess
ap=argparse.ArgumentParser();ap.add_argument('--logical-gib',type=int,default=128);a=ap.parse_args()
assert os.environ.get('GITHUB_ACTIONS')=='true'
assert os.environ.get('RUNNER_ENVIRONMENT')=='github-hosted' and os.environ.get('RUNNER_OS')=='Linux'
workspace=pathlib.Path(os.environ['GITHUB_WORKSPACE']).resolve()
assert workspace.is_relative_to('/home/runner/work') and workspace.is_dir()
assert 4<=a.logical_gib<=256
image=workspace/'rg-ephemeral-proofstore.btrfs'
mount=workspace/'Proofs/RG_Lean_20261019/build/extension'
assert not image.exists() and not image.is_symlink()
mount.mkdir(parents=True,exist_ok=True)
assert not mount.is_symlink() and mount.resolve().is_relative_to(workspace) and not any(mount.iterdir())
assert shutil.disk_usage(workspace).free>=12*1024**3
assert shutil.which('mkfs.btrfs') and shutil.which('mount')
before=shutil.disk_usage(workspace).free
with image.open('xb') as stream:stream.truncate(a.logical_gib*1024**3)
identity=image.stat()
assert identity.st_size==a.logical_gib*1024**3 and image.resolve()==image
subprocess.run(['sudo','mkfs.btrfs','-d','single','-m','dup','-L','RG_EPHEMERAL_PROOFS',str(image)],check=True)
now=image.stat();assert (now.st_dev,now.st_ino)==(identity.st_dev,identity.st_ino)
subprocess.run(['sudo','mount','-o','loop,compress=zstd:6',str(image),str(mount)],check=True)
subprocess.run(['sudo','chown',f'{os.getuid()}:{os.getgid()}',str(mount)],check=True)
filesystem=json.loads(subprocess.check_output(['findmnt','-J','-T',str(mount)],text=True))['filesystems'][0]
assert filesystem['fstype']=='btrfs' and 'compress=zstd:6' in filesystem['options']
report=dict(status='NEW_EPHEMERAL_COMPRESSED_PROOFSTORE_MOUNTED',image=str(image),mount=str(mount),
    logical_image_bytes=image.stat().st_size,allocated_image_bytes=image.stat().st_blocks*512,
    host_free_before=before,host_free_after=shutil.disk_usage(workspace).free,
    filesystem=filesystem,compression_ratio='UNMEASURED_NOT_A_CAPACITY_GUARANTEE',local_changes=0,
    existing_sources_or_archives_deleted=0,mathematical_checks_changed=False)
(workspace/'rg-proofstore-setup.json').write_text(json.dumps(report,indent=2)+'\n')
with open(os.environ['GITHUB_ENV'],'a') as stream:stream.write('RG_PROOFSTORE_HOST_PATH='+str(workspace)+'\n')
print(json.dumps(report),flush=True)
