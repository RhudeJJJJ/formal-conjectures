"""Change only compilation eligibility of two original anchor028 data constants."""
import argparse,hashlib,json,pathlib,re,shutil
R=pathlib.Path(__file__).resolve().parent.parent;S=R/'Proofs/RG_Lean_20261019'
ap=argparse.ArgumentParser();ap.add_argument('--endpoint',required=True);a=ap.parse_args()
assert a.endpoint=='Proofs.RadenkovicGutmanWideAnchor028OriginalAnchor'
bundle=S/'build/fresh_exports/generated_source';mp=bundle/'generated_source_manifest.json'
m=json.loads(mp.read_bytes());assert m['endpoint']==a.endpoint and m['anchor_index']==28
assert m['kind']=='ORIGINAL_TARGET_REQUIRES_SUCCESSFUL_KERNEL_RECEIPT'
assert shutil.disk_usage(R).free>8*1024**3+1024**2
edits=[]
for suffix in ['Source','PositiveTail']:
    rel='Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanWideAnchor028'+suffix+'.lean'
    path=R/rel;before=path.read_bytes();old=b'\ndef data : ComputedGeneralPathData.Data :=';new=b'\nnoncomputable def data : ComputedGeneralPathData.Data :='
    assert before.count(old)==1 and new not in before
    assert hashlib.sha256(before).hexdigest()==m['source_sha256'][rel]
    assert (bundle/rel).read_bytes()==before
    after=before.replace(old,new)
    assert after.replace(new,old)==before
    # The complete proof and every type/value token stay byte-identical after
    # deleting the sole noncomputable modifier. No data or certificate is trusted.
    retained=bundle/'before_noncomputable_data'/rel;retained.parent.mkdir(parents=True,exist_ok=True);assert not retained.exists();retained.write_bytes(before)
    path.write_bytes(after);(bundle/rel).write_bytes(after)
    digest=hashlib.sha256(after).hexdigest();m['source_sha256'][rel]=digest
    edits.append(dict(path=rel,before_sha256=hashlib.sha256(before).hexdigest(),after_sha256=digest,only_change='noncomputable modifier on data definition; all types, values and proofs identical'))
m['compilation_only_control']=dict(original_anchor_index=28,edits=edits,raw_original_sources_retained=True,all_original_kernel_obligations_retained=True,memory_improvement='NOT_ASSUMED_REQUIRES_MEASURED_KERNEL_RESULT')
mp.write_bytes((json.dumps(m,indent=2)+'\n').encode())
print(json.dumps(dict(status='ONLY_TWO_DATA_COMPILATION_MODIFIERS_CHANGED_REQUIRES_FULL_ORIGINAL_KERNEL_CHECK',endpoint=a.endpoint,edits=edits,original_target_unchanged=True,whole_anchor='OPEN',universal_RG='OPEN',complete_submission='NOT_SUBMITTED')),flush=True)
