"""Retain complete successful module outputs and unabridged compiler diagnostics."""
import argparse,hashlib,json,pathlib,shutil,sys
repo=pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0,str(repo/'Proofs/RG_Lean_20261019'))
from module_outputs import output_members
ap=argparse.ArgumentParser();ap.add_argument('--build-directory',type=pathlib.Path,required=True)
ap.add_argument('--output-directory',type=pathlib.Path,required=True);a=ap.parse_args()
root=a.build_directory.resolve();dest=a.output_directory.resolve();dest.mkdir(parents=True,exist_ok=True)
assert root!=dest and root.is_relative_to(repo) and dest.is_relative_to(repo)
records=[json.loads(p.read_text()) for p in sorted(root.glob('Proofs.*.json'))]
(dest/'diagnostics_records.json').write_text(json.dumps({'modules':records},separators=(',',':'))+'\n')
if (root/'receipt.json').is_file():shutil.copyfile(root/'receipt.json',dest/'receipt.json')
count=0;sidecars=0;logical=0
for row in records:
 if row['mode']!='FRESH_KERNEL_EXPORT':continue
 n=row['module'];count+=1
 assert row['axiom_profiles'] and all(set(ax)<={'propext','Classical.choice','Quot.sound'} for ax in row['axiom_profiles'])
 for rel,expected_sha,expected_size in output_members(n,row):
  source=root/rel;target=dest/rel
  assert source.resolve().is_relative_to(root) and target.resolve().is_relative_to(dest)
  assert expected_size is None or source.stat().st_size==expected_size
  with source.open('rb') as f:assert hashlib.file_digest(f,'sha256').hexdigest()==expected_sha,rel
  logical+=source.stat().st_size;assert logical<=8*1024**3
  target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source,target)
  if rel.endswith(('.server','.private')):sidecars+=1
 shutil.copyfile(root/(n+'.json'),dest/(n+'.json'))
for log in root.glob('Proofs.*.log'):
 shutil.copyfile(log,dest/log.name)
 print('MODULE_LOG_TAIL '+log.name+' '+log.read_text()[-18000:])
print('RETAINED_RECORD_COUNTS '+json.dumps({'total':len(records),'fresh':count,'sidecars':sidecars,'logical_output_bytes':logical}))
