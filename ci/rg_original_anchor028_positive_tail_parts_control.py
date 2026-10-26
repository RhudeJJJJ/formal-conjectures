"""Preserve the original anchor028 target and split only its tail-check proof."""
import argparse,hashlib,json,pathlib,shutil
ap=argparse.ArgumentParser();ap.add_argument('--endpoint',required=True);ap.add_argument('--project-root',type=pathlib.Path);a=ap.parse_args()
R=(a.project_root or pathlib.Path(__file__).resolve().parent.parent).resolve();S=R/'Proofs/RG_Lean_20261019'
assert a.endpoint=='Proofs.RadenkovicGutmanWideAnchor028OriginalAnchor'
bundle=S/'build/fresh_exports/generated_source';mp=bundle/'generated_source_manifest.json';m=json.loads(mp.read_bytes())
assert m['endpoint']==a.endpoint and m['anchor_index']==28 and m['kind']=='ORIGINAL_TARGET_REQUIRES_SUCCESSFUL_KERNEL_RECEIPT'
assert 'compilation_only_control' not in m and len(m['source_sha256'])==153
assert shutil.disk_usage(R).free>8*1024**3+64*1024**2
rel='Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanWideAnchor028PositiveTail.lean';path=R/rel;before=path.read_bytes()
assert hashlib.sha256(before).hexdigest()==m['source_sha256'][rel]=='45baf2f29c14632ce8aa1bd4882e94f46e480a2d579e7d61f1b6a042c8b7985a'
assert (bundle/rel).read_bytes()==before
source_rel='Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanWideAnchor028Source.lean'
assert hashlib.sha256((R/source_rel).read_bytes()).hexdigest()==m['source_sha256'][source_rel]=='fdc9ef4f6fd76290ffc6e7c780229b48097182edcaa7c02462b9623eac57796e'
NEW_SOURCES={'Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanPositiveTailParts.lean': 'ed334b3add6f23d58f252696b5e7c7e8ddd328f93f934a9b5d0152795058a51a', 'Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanWideAnchor028PositiveTailPartsData.lean': 'f459811c77c692632b09e5c102a3e0722b43f232bcbff95140a6fd659dbe97a5', 'Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanWideAnchor028PositiveTailPart00.lean': 'f8602cfaa858140245a3b2b9d256b732b05b793e1339572eb86e1cd78734a63d', 'Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanWideAnchor028PositiveTailPart01.lean': '94728a690978f98d85f370c9b10b49a497cb375b69d1a197762bce4eeb114f6a', 'Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanWideAnchor028PositiveTailPart02.lean': 'b0512210607afed446336b74f6a8771a8b5f05ad594ed96a5755763f777612ba', 'Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanWideAnchor028PositiveTailPart03.lean': 'cfac46819b4cabcc866371b9fba4d4c3578387e525e5d76bd5622534d376e2e3', 'Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanWideAnchor028PositiveTailPart04.lean': 'b8bf9bdf968bccd12f7936f8b70e0e3a2d28397a52a137b9c5c12d06a2f4d053', 'Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanWideAnchor028PositiveTailPart05.lean': 'ffc0584e72d8e2ed37779cc729c2a615e3741b18d782e5707b2f37599bdf5ef6', 'Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanWideAnchor028PositiveTailPart06.lean': 'cfcf159a71feaea4c57534e40d3eab254b509e4d9c8a99e258827fe393730d9c', 'Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanWideAnchor028PositiveTailParts.lean': '95f8c16ef184f9d6631a0b8e2172270bba5e690fc179f67696cbb3344584ff4e'}
for p,digest in NEW_SOURCES.items():
    raw=(R/p).read_bytes();assert hashlib.sha256(raw).hexdigest()==digest and p not in m['source_sha256']
    target=bundle/p;target.parent.mkdir(parents=True,exist_ok=True)
    if target.exists():assert target.read_bytes()==raw
    else:target.write_bytes(raw)
    m['source_sha256'][p]=digest
old='theorem checked : ComputedPositiveTail.checks data K Y=true := by decide +kernel\n';new='theorem checked : ComputedPositiveTail.checks data K Y=true := by\n  simpa only [data,K,Y,WideAnchor028PositiveTailPartsData.data,WideAnchor028PositiveTailPartsData.K,WideAnchor028PositiveTailPartsData.Y] using\n    WideAnchor028PositiveTailParts.checked\n';added_import='import Proofs.RadenkovicGutmanWideAnchor028PositiveTailParts\n'
text=before.decode();assert text.count(old)==1
after=text.replace('import Proofs.RadenkovicGutmanComputedPositiveTail\n','import Proofs.RadenkovicGutmanComputedPositiveTail\n'+added_import,1).replace(old,new,1)
assert after.replace(added_import,'',1).replace(new,old,1)==text
assert after[after.index('noncomputable section'):]==text[text.index('noncomputable section'):]
retained=bundle/'before_positive_tail_parts'/path.name;retained.parent.mkdir(parents=True,exist_ok=True);assert not retained.exists();retained.write_bytes(before)
path.write_bytes(after.encode());(bundle/rel).write_bytes(after.encode());m['source_sha256'][rel]=hashlib.sha256(after.encode()).hexdigest()
assert len(m['source_sha256'])==163
m['positive_tail_proof_decomposition_control']=dict(original_anchor_index=28,original_tail_source_sha256=hashlib.sha256(before).hexdigest(),new_tail_source_sha256=m['source_sha256'][rel],new_module_source_sha256=NEW_SOURCES,all_original_data_bounds_targets_and_integral_proofs_unchanged=True,original_source_data_module_unchanged=True,original_checked_statement_unchanged=True,required_original_conditions=7,all_conditions_reassembled_by_kernel_lemma=True,memory_improvement='NOT_ASSUMED_REQUIRES_MEASURED_KERNEL_RESULT')
mp.write_bytes((json.dumps(m,indent=2)+'\n').encode())
print(json.dumps(dict(status='ORIGINAL_TAIL_CHECK_SPLIT_INTO_SEVEN_KERNEL_CONDITIONS_REQUIRES_FULL_ORIGINAL_CHECK',endpoint=a.endpoint,new_modules=10,max_fresh=163,original_target_unchanged=True,whole_anchor='OPEN',submission='NOT_SUBMITTED')),flush=True)
