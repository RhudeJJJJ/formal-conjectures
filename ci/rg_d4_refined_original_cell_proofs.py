"""Materialize the reduced original degree-four cover with all kernel checks."""
import argparse,hashlib,json,pathlib,re,shutil
from fractions import Fraction as Q
from rg_fixed_degree_compositional_cells import cell_sources,power_sources,slice_wrapper
R=pathlib.Path(__file__).resolve().parent.parent;S=R/'Proofs/RG_Lean_20261019'
DATA='ci/rg_d4_refined_original_square_candidates.json'
def build(group,half=None):
    packet=json.loads((R/DATA).read_bytes());row=packet['groups'][group]
    assert row['group']==group and packet['original_normalized_reserve']=='2/13'
    if row['candidate_nonnegative']:
        assert half is None
        index=4*group;ns=f'D4FullParameterGroup{group:04d}';root='Proofs.RadenkovicGutman'+ns
        cell=row['cell'];assert Q(cell['payment'])>=Q(row['original_slice_payment'])
        sources=cell_sources(4,index,cell,root,ns)
        if row['affine_power_candidate_nonnegative']:
            new_ns=f'D4PowerParameterGroup{group:04d}';new_root='Proofs.RadenkovicGutman'+new_ns
            sources=power_sources(index,sources,root,ns,new_root,new_ns);root,ns=new_root,new_ns
            maximum=65
        else:maximum=154
        sources[root+'Complete']=slice_wrapper(4,index,ns,*row['interval'],row['original_slice_payment'])
        assert len(sources)==maximum
        return root+'Complete',maximum,sources
    assert group==164 and half in [0,1]
    ns=f'D4OriginalFallbackGroup{group:04d}';sources={};deps=[];names=[]
    for local in range(2*half,2*half+2):
        index=4*group+local;cell=packet['fallback_cells'][str(group)][local]
        root='Proofs.RadenkovicGutman'+ns+f'Leaf{index:05d}'
        sources.update(cell_sources(4,index,cell,root,ns));deps.append(root);names.append(f'leaf{index:05d}')
    endpoint='Proofs.RadenkovicGutman'+ns+f'Half{half}'
    sources[endpoint]='/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/\n'+''.join('import '+e+'\n' for e in deps)+f'''namespace Gebendorfer.RadenkovicGutman.{ns}
theorem half{half}_checked : FastNestedCellData.accepts 4 4 4 {names[0]}=true ∧
    FastNestedCellData.accepts 4 4 4 {names[1]}=true :=
  ⟨{names[0]}_checked,{names[1]}_checked⟩
#print axioms half{half}_checked
end Gebendorfer.RadenkovicGutman.{ns}
'''
    assert len(sources)==307
    return endpoint,307,sources
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--endpoint',required=True);a=ap.parse_args()
    normal=re.fullmatch(r'Proofs\.RadenkovicGutmanD4(?:FullParameterGroup|PowerParameterGroup)(\d{4})Complete',a.endpoint)
    half=re.fullmatch(r'Proofs\.RadenkovicGutmanD4OriginalFallbackGroup(\d{4})Half([01])',a.endpoint)
    assert normal or half
    registry=json.loads((R/'ci/rg_d4_refined_original_cells_source_registry.json').read_bytes())
    for row in registry['source_inputs']:assert hashlib.sha256((R/row['path']).read_bytes()).hexdigest()==row['sha256'],row['path']
    group=int((normal or half)[1]);endpoint,maximum,sources=build(group,None if normal else int(half[2]))
    assert endpoint==a.endpoint and maximum==registry['endpoints'][endpoint]['max_fresh']
    assert shutil.disk_usage(R).free>8*1024**3+16*1024**2
    total=0;hashes={};bundle=S/'build/fresh_exports/generated_source'
    for n,t in sources.items():
        raw=t.encode();total+=len(raw);digest=hashlib.sha256(raw).hexdigest();assert digest==registry['sources'][n],n
        rel='Proofs/RG_Lean_20261019/'+n.replace('.','/')+'.lean';p=R/rel
        if p.exists():assert p.read_bytes()==raw,n
        else:p.write_bytes(raw)
        target=bundle/rel;target.parent.mkdir(parents=True,exist_ok=True)
        if target.exists():assert target.read_bytes()==raw
        else:target.write_bytes(raw)
        hashes[rel]=digest
    assert total<16*1024**2
    (bundle/'generated_source_manifest.json').write_bytes((json.dumps(dict(endpoint=endpoint,original_group=group,original_class_indices=[4,4],source_sha256=hashes,kind='CANDIDATES_REQUIRE_SUCCESSFUL_KERNEL_RECEIPT'),indent=2)+'\n').encode())
    print(json.dumps(dict(status='ORIGINAL_DEGREE4_INTERVAL_PROOFS_REQUIRE_KERNEL',endpoint=endpoint,group=group,modules=len(sources),source_bytes=total,whole_class='OPEN',universal_rg='OPEN')),flush=True)
if __name__=='__main__':main()
