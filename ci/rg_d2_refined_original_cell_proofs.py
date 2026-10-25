"""Ordinary Lean source for the original degree-two cover; no native proof trust."""
import argparse, hashlib, json, pathlib, re, shutil
from fractions import Fraction as Q
from rg_fixed_degree_compositional_cells import cell_sources, power_sources, slice_wrapper
R=pathlib.Path(__file__).resolve().parent.parent
S=R/'Proofs/RG_Lean_20261019'
DATA='ci/rg_d2_refined_original_square_candidates.json'

def build(group,part=None):
    packet=json.loads((R/DATA).read_bytes());row=packet['groups'][group]
    assert row['group']==group and packet['original_normalized_reserve']=='1/9'
    first=row['original_first_leaf']
    if row['candidate_nonnegative']:
        assert part is None
        ns=f'D2FullParameterGroup{group:04d}';root='Proofs.RadenkovicGutman'+ns
        cell=row['cell'];assert Q(cell['payment'])>=Q(row['original_slice_payment'])
        sources=cell_sources(2,first,cell,root,ns)
        if row['affine_power_candidate_nonnegative']:
            new_ns=f'D2PowerParameterGroup{group:04d}';new_root='Proofs.RadenkovicGutman'+new_ns
            sources=power_sources(first,sources,root,ns,new_root,new_ns);root,ns=new_root,new_ns
            maximum=65
        else:maximum=154
        sources[root+'Complete']=slice_wrapper(2,first,ns,*row['interval'],row['original_slice_payment'])
        assert len(sources)==maximum
        return root+'Complete',maximum,sources
    cells=packet['fallback_cells'][str(group)]
    assert part is not None and 0<=part<(len(cells)+1)//2
    ns=f'D2OriginalFallbackGroup{group:04d}';sources={};deps=[];names=[]
    for local in range(2*part,min(2*part+2,len(cells))):
        index=first+local;root='Proofs.RadenkovicGutman'+ns+f'Leaf{index:05d}'
        sources.update(cell_sources(2,index,cells[local],root,ns));deps.append(root);names.append(f'leaf{index:05d}')
    endpoint='Proofs.RadenkovicGutman'+ns+f'Part{part:02d}'
    propositions=[f'FastNestedCellData.accepts 2 4 4 {n}=true' for n in names]
    proof=names[0]+'_checked' if len(names)==1 else '⟨'+','.join(n+'_checked' for n in names)+'⟩'
    sources[endpoint]='/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/\n'+''.join('import '+e+'\n' for e in deps)+f'''namespace Gebendorfer.RadenkovicGutman.{ns}
theorem part{part:02d}_checked : {' ∧ '.join(propositions)} :=
  {proof}
#print axioms part{part:02d}_checked
end Gebendorfer.RadenkovicGutman.{ns}
'''
    maximum=153*len(names)+1;assert len(sources)==maximum
    return endpoint,maximum,sources

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--endpoint',required=True);a=ap.parse_args()
    normal=re.fullmatch(r'Proofs\.RadenkovicGutmanD2(?:FullParameterGroup|PowerParameterGroup)(\d{4})Complete',a.endpoint)
    part=re.fullmatch(r'Proofs\.RadenkovicGutmanD2OriginalFallbackGroup(\d{4})Part(\d{2})',a.endpoint)
    assert normal or part
    group=int((normal or part)[1]);registry=json.loads((R/f'ci/rg_d2_refined_original_cells_part{group//225}_registry.json').read_bytes())
    for row in registry['source_inputs']:
        assert hashlib.sha256((R/row['path']).read_bytes()).hexdigest()==row['sha256'],row['path']
    endpoint,maximum,sources=build(group,None if normal else int(part[2]))
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
    print(json.dumps(dict(status='ORIGINAL_DEGREE2_INTERVAL_PROOFS_REQUIRE_KERNEL',endpoint=endpoint,modules=len(sources),source_bytes=total,whole_class='OPEN',universal_rg='OPEN')),flush=True)
if __name__=='__main__':main()
