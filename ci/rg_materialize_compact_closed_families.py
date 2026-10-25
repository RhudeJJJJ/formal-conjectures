"""Reproduce source-hashed closed-family callers; all changed callers are fresh."""
import argparse,hashlib,json,pathlib,re,shutil
R=pathlib.Path(__file__).resolve().parents[1];S=R/'Proofs/RG_Lean_20261019'
ap=argparse.ArgumentParser();ap.add_argument('--endpoint',required=True);ap.add_argument('--max-raw-mib',type=int,default=128);a=ap.parse_args()
assert re.fullmatch(r'Proofs\.RadenkovicGutmanCompactFinite\w+',a.endpoint)
assert 1<=a.max_raw_mib<=512 and shutil.disk_usage(R).free>8*1024**3+a.max_raw_mib*1024**2
def sha(b):return hashlib.sha256(b).hexdigest()
g=json.loads((R/'ci/rg_compact_closed_families_source_registry.json').read_bytes())
assert g['kind']=='EXACT_CLOSED_ORIGINAL_FAMILIES_IMPORT_REPLAY'
raw=(R/'ci/rg_compact_finite_source_registry.json').read_bytes();assert sha(raw)==g['finite_registry_sha256'];f=json.loads(raw)
entries={**f['entries'],**g['entries']};mapping={v['original']:n for n,v in entries.items()}
assert len(mapping)==len(entries)
seen=set();written=0
def visit(n):
    global written
    if n in seen:return
    seen.add(n)
    if n in entries:
        row=entries[n];raw=(S/(row['original'].replace('.','/')+'.lean')).read_bytes();assert sha(raw)==row['original_source_sha256'],n
        text=raw.decode()
        for d in re.findall(r'^\s*import\s+(Proofs\.[\w.]+)\s*$',text,re.M):
            if d in mapping:text=text.replace('import '+d+'\n','import '+mapping[d]+'\n')
        if row['numerical']:
            for name in f['data_definitions']:
                text,count=re.subn(r'^def '+name+r'\b','noncomputable def '+name,text,count=1,flags=re.M);assert count==1
        raw=text.encode();assert sha(raw)==row['source_sha256'],n
        target=S/(n.replace('.','/')+'.lean')
        if target.exists():assert target.read_bytes()==raw,n
        else:target.write_bytes(raw)
        written+=len(raw);assert written<=a.max_raw_mib*1024**2
    else:
        raw=(S/(n.replace('.','/')+'.lean')).read_bytes();assert n in g['unaffected_sources'] and sha(raw)==g['unaffected_sources'][n],n
    for d in re.findall(r'^\s*import\s+(Proofs\.[\w.]+)\s*$',raw.decode(),re.M):
        assert d not in mapping,('Mixed original/replayed numerical dependency',n,d)
        visit(d)
visit(a.endpoint)
print(json.dumps(dict(status='EXACT_CLOSED_FAMILY_IMPORT_REPLAY_MATERIALIZED_REQUIRES_KERNEL',endpoint=a.endpoint,modules=len(seen),replayed_source_bytes=written,original_namespaces_and_theorem_bodies_unchanged=True,mathematical_coverage_added=0)),flush=True)
