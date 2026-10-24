"""Reproduce the exact source-hashed finite scope; never reuse changed proof objects."""
import argparse,hashlib,json,pathlib,re,shutil
R=pathlib.Path(__file__).resolve().parent.parent;S=R/'Proofs/RG_Lean_20261019'
ap=argparse.ArgumentParser();ap.add_argument('--endpoint',required=True)
ap.add_argument('--max-raw-mib',type=int,default=512);a=ap.parse_args()
assert re.fullmatch(r'Proofs\.RadenkovicGutmanCompactFinite\w+',a.endpoint)
assert 1<=a.max_raw_mib<=1024 and shutil.disk_usage(R).free>8*1024**3+a.max_raw_mib*1024**2
m=json.loads((R/'ci/rg_compact_finite_source_registry.json').read_bytes())
assert m['kind']=='EXACT_ORIGINAL_FINITE_SOURCE_REPLAY_NONCOMPUTABLE_DATA_ONLY'
entries=m['entries'];original_to_variant={v['original']:n for n,v in entries.items()}
batches={x['endpoint']:x for x in m['numeric_batches']}
seen=set();written=0

def sha(raw):return hashlib.sha256(raw).hexdigest()

def materialize(n):
    global written
    row=entries[n];path=S/(row['original'].replace('.','/')+'.lean');raw=path.read_bytes()
    assert sha(raw)==row['original_source_sha256'],row['original']
    text=raw.decode()
    for dep in re.findall(r'^\s*import\s+(Proofs\.[\w.]+)\s*$',text,re.M):
        if dep in original_to_variant:text=text.replace('import '+dep+'\n','import '+original_to_variant[dep]+'\n')
    if row['numerical']:
        for name in m['data_definitions']:
            text,count=re.subn(r'^def '+name+r'\b','noncomputable def '+name,text,count=1,flags=re.M)
            assert count==1,(n,name)
    blob=text.encode();assert sha(blob)==row['source_sha256'],n
    target=S/(n.replace('.','/')+'.lean')
    if target.exists():assert target.read_bytes()==blob,n
    else:target.write_bytes(blob)
    written+=len(blob);assert written<=a.max_raw_mib*1024**2

def visit(n):
    if n in seen:return
    seen.add(n)
    if n in entries:materialize(n)
    raw=(S/(n.replace('.','/')+'.lean')).read_bytes()
    if n in m['unaffected_sources']:assert sha(raw)==m['unaffected_sources'][n],n
    elif n in batches:assert sha(raw)==batches[n]['source_sha256'],n
    else:assert n in entries,n
    for dep in re.findall(r'^\s*import\s+(Proofs\.[\w.]+)\s*$',raw.decode(),re.M):
        assert dep not in original_to_variant,('Refuse mixed original and replayed numerical dependencies',n,dep)
        visit(dep)
visit(a.endpoint)
print(json.dumps(dict(status='EXACT_SOURCE_SCOPE_MATERIALIZED_REQUIRES_FRESH_KERNEL_CHECKS',endpoint=a.endpoint,modules=len(seen),selected_raw_source_bytes=written,original_theorem_bodies_unchanged=True,namespace_integration='Use the same source-import mapping throughout every later caller; do not combine original and replayed versions',mathematical_coverage_added=0)),flush=True)
