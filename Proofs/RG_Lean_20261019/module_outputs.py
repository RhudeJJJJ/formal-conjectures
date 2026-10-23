"""Keep every Lean module output, including exported module-system sidecars."""
import hashlib,pathlib,re

KINDS=('server','private')
def digest_file(path):
 with pathlib.Path(path).open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def side_path(path,kind):
 assert kind in KINDS
 path=pathlib.Path(path);return path.with_name(path.name+'.'+kind)
def extra_specs(row):
 specs=row.get('additional_outputs',{})
 assert isinstance(specs,dict) and set(specs)<=set(KINDS)
 for kind,info in specs.items():
  assert isinstance(info,dict) and set(info)=={'sha256','bytes'}
  assert re.fullmatch(r'[0-9a-f]{64}',info['sha256'])
  assert isinstance(info['bytes'],int) and info['bytes']>=0
 return specs
def check_additional_outputs(out,row):
 for kind,info in extra_specs(row).items():
  p=side_path(out,kind)
  assert p.is_file() and p.stat().st_size==info['bytes'],f'Missing or resized module sidecar: {p}'
  assert digest_file(p)==info['sha256'],f'Changed module sidecar: {p}'
def remove_pending_outputs(tmp):
 tmp=pathlib.Path(tmp)
 for kind in KINDS:side_path(tmp,kind).unlink(missing_ok=True)
 tmp.unlink(missing_ok=True)
def finalize_outputs(tmp,out):
 """Call only after successful strict compilation and source/profile checks."""
 tmp,out=pathlib.Path(tmp),pathlib.Path(out);specs={}
 assert tmp.parent.resolve()==out.parent.resolve() and tmp.is_file()
 for kind in KINDS:
  pending=side_path(tmp,kind);target=side_path(out,kind)
  if pending.exists():
   assert pending.is_file()
   info={'sha256':digest_file(pending),'bytes':pending.stat().st_size}
   pending.replace(target);specs[kind]=info
  else:
   target.unlink(missing_ok=True)
 tmp.replace(out)
 return specs
def output_members(name,row):
 assert re.fullmatch(r'(?:Proofs|LeanCert)(?:\.[A-Za-z0-9_]+)+',name),name
 rel=name.replace('.','/')+'.olean'
 yield rel,row['output_sha256'],None
 for kind,info in extra_specs(row).items():yield rel+'.'+kind,info['sha256'],info['bytes']

def check_archive_outputs(archive,name,row):
 """The caller must separately authenticate the complete original archive."""
 logical=0
 for rel,expected_sha,expected_size in output_members(name,row):
  info=archive.getinfo(rel)
  assert expected_size is None or info.file_size==expected_size,(name,rel)
  with archive.open(rel) as f:assert hashlib.file_digest(f,'sha256').hexdigest()==expected_sha,(name,rel)
  logical+=info.file_size
 return logical
