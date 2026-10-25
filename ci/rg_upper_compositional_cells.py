"""Checked-source materializer for the original upper-degree long-long target."""
import argparse,hashlib,json,pathlib,re,shutil
from fractions import Fraction as Q
from rg_fixed_degree_compositional_cells import cell_sources,power_sources,slice_wrapper,integer_norm_source
R=pathlib.Path(__file__).resolve().parent.parent;S=R/'Proofs/RG_Lean_20261019'
def build(degree,index):
    assert 5<=degree<=45
    packet=json.loads((R/f'ci/rg_upper_long_original_degree{degree:02d}_cell_recipes.json').read_bytes())
    assert packet['report']['degree']==degree and packet['report']['class_indices']==[4,4]
    assert packet['report']['normalized_original_reserve']=='2/13'
    row=packet['cells'][index];assert row['kind']=='polynomial'
    assert list(map(Q,row['box_left'][1:]))==[Q(0),Q(0)] and list(map(Q,row['box_width'][1:]))==[Q(1),Q(1)]
    cell={k:row[k] for k in ['young','square_lower','payment','logarithm_k','logarithm_n','reciprocal','box_left','box_width']}
    cell['degrees']=[88,4,4]
    ns=f'D{degree}UpperFullSquareCell{index:04d}';root='Proofs.RadenkovicGutman'+ns
    sources=cell_sources(degree,index,cell,root,ns)
    if row['affine_power_candidate_nonnegative']:
        new_ns=f'D{degree}UpperPowerSquareCell{index:04d}';new_root='Proofs.RadenkovicGutman'+new_ns
        sources=power_sources(index,sources,root,ns,new_root,new_ns);root,ns=new_root,new_ns
        maximum=66
    else:maximum=155
    sources[root+'Complete']=slice_wrapper(degree,index,ns,row['left'],row['right'],row['payment'])
    name,text=integer_norm_source(degree);sources[name]=text
    assert len(sources)==maximum
    return root+'Complete',maximum,sources
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--endpoint',required=True);a=ap.parse_args()
    match=re.fullmatch(r'Proofs\.RadenkovicGutmanD(\d+)Upper(?:Full|Power)SquareCell(\d{4})Complete',a.endpoint);assert match
    degree,index=map(int,match.groups())
    registry=json.loads((R/f'ci/rg_upper_long_original_degree{degree:02d}_source_registry.json').read_bytes())
    for row in registry['source_inputs']:assert hashlib.sha256((R/row['path']).read_bytes()).hexdigest()==row['sha256'],row['path']
    endpoint,maximum,sources=build(degree,index)
    assert endpoint==a.endpoint and maximum==registry['endpoints'][endpoint]['max_fresh']
    assert shutil.disk_usage(R).free>8*1024**3+16*1024**2
    total=0;hashes={};bundle=S/'build/fresh_exports/generated_source'
    for name,text in sources.items():
        raw=text.encode();total+=len(raw);digest=hashlib.sha256(raw).hexdigest();assert digest==registry['sources'][name],name
        rel='Proofs/RG_Lean_20261019/'+name.replace('.','/')+'.lean';target=R/rel
        if target.exists():assert target.read_bytes()==raw,name
        else:target.write_bytes(raw)
        copied=bundle/rel;copied.parent.mkdir(parents=True,exist_ok=True)
        if copied.exists():assert copied.read_bytes()==raw
        else:copied.write_bytes(raw)
        hashes[rel]=digest
    assert total<16*1024**2
    (bundle/'generated_source_manifest.json').write_bytes((json.dumps(dict(endpoint=endpoint,degree=degree,candidate_cell_index=index,original_class_indices=[4,4],source_sha256=hashes,kind='CANDIDATES_REQUIRE_SUCCESSFUL_KERNEL_RECEIPT'),indent=2)+'\n').encode())
    print(json.dumps(dict(status='ORIGINAL_UPPER_CLASS_CELL_REQUIRES_KERNEL',endpoint=endpoint,degree=degree,index=index,modules=len(sources),source_bytes=total,original_target='2/13',whole_class='OPEN',universal_rg='OPEN')),flush=True)
if __name__=='__main__':main()
