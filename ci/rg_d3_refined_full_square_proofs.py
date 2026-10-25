"""Materialize ordinary checked Lean sources for the original degree-three cover.

The host candidates are data only. Every polynomial operation, degree bound,
coefficient sign, logarithm, cell acceptance and actual-graph bridge is checked.
"""
import argparse,functools,hashlib,json,pathlib,re,shutil
from fractions import Fraction as Q
from rg_compositional_d1_repair import build as original_build
R=pathlib.Path(__file__).resolve().parent.parent
S=R/'Proofs/RG_Lean_20261019'
DATA='ci/rg_d3_refined_original_full_square_candidates.json'
PACKET='ci/rg_d3_both_long_no_runtime_exact_source_recipes.json'
def rat(v):
    q=Q(v)
    return str(q.numerator) if q.denominator==1 else f'({q.numerator}/{q.denominator})'
@functools.lru_cache(maxsize=1)
def inputs():
    report=json.loads((R/DATA).read_bytes())
    assert report['search_complete'] and report['processed']==951
    raw=(R/PACKET).read_bytes()
    assert hashlib.sha256(raw).hexdigest()==report['original_recipe_sha256']
    assert report['full_parameter_candidate_passes']==948
    assert [x['group'] for x in report['groups'] if not x['candidate_nonnegative']]==[805,806,807]
    return report,json.loads(raw)
def cell_sources(index,cell,root,ns):
    old=f'Proofs.RadenkovicGutmanD1Long00Leaf{index:05d}CompositionalRepair'
    result={}
    for n,t in original_build(index,cell).items():
        text=t.replace(old,root).replace('DegreeOneLongClass00',ns).replace('DegreeOneIntegerNorm00.pack','FixedDegree03Long00StagedIntegerNorm.pack').replace('DegreeOneNormPack00.pack','FixedDegree03Long00StagedNormPack.pack').replace('import Proofs.RadenkovicGutmanD1IntegerNorm00','import Proofs.RadenkovicGutmanD3Long00StagedIntegerNorm')
        if n==old:
            assert text.count('FastNestedCellData.accepts 1 4 4')==1
            text=text.replace('FastNestedCellData.accepts 1 4 4','FastNestedCellData.accepts 3 4 4')
        result[n.replace(old,root)]=text
    assert len(result)==153
    return result
def wrapper(group,ns,index):
    text=(R/'ci/rg_d3_original_square_wrapper.lean.txt').read_text()
    report,_=inputs();zero=report['groups'][0];row=report['groups'][group]
    assert Q(row['interval'][0])<Q(row['interval'][1])
    replacements=dict(zip(map(rat,[*zero['interval'],zero['original_slice_payment']]),map(rat,[*row['interval'],row['original_slice_payment']])))
    assert len(replacements)==3 and all(token in text for token in replacements)
    tokens=re.compile('|'.join(re.escape(x) for x in sorted(replacements,key=len,reverse=True)))
    text=tokens.sub(lambda m:replacements[m[0]],text)
    return text.replace('D3FullParameterGroup0000',ns).replace('leaf00000',f'leaf{index:05d}')
def full(group,report):
    row=report['groups'][group];assert row['group']==group and row['candidate_nonnegative']
    index=4*group;cell=row['cell'];assert cell['box_left'][1:]==['0','0'] and cell['box_width'][1:]==['1','1']
    assert Q(cell['payment'])>=Q(row['original_slice_payment'])
    old_ns=f'D3FullParameterGroup{group:04d}';root='Proofs.RadenkovicGutman'+old_ns
    sources=cell_sources(index,cell,root,old_ns)
    if row['affine_power_candidate_nonnegative']:
        tail=sources[root];tail=tail[tail.index(f'theorem leaf{index:05d}_log :'):]
        ns=f'D3PowerParameterGroup{group:04d}';endpoint='Proofs.RadenkovicGutman'+ns
        tail=tail.replace('end Gebendorfer.RadenkovicGutman.'+old_ns,'end Gebendorfer.RadenkovicGutman.'+ns)
        text=f'''/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import {root}AffineLength
import Proofs.RadenkovicGutmanPowerBernstein
namespace Gebendorfer.RadenkovicGutman.{ns}
open {old_ns}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem leaf{index:05d}_sign : NestedInteger.bernsteinCheck 3 ![88,4,4] leaf{index:05d}_w_affine=true :=
  PowerBernstein.checked 3 ![88,4,4] leaf{index:05d}_w_affine
    (by decide +kernel) (by decide +kernel)
#print axioms leaf{index:05d}_sign
'''+tail
        sources={n:t for n,t in sources.items() if n!=root and not re.fullmatch(re.escape(root)+r'Row\d{3}',n)}
        assert len(sources)==63
        sources[endpoint]=text
        sources[endpoint+'Complete']=wrapper(group,ns,index)
        assert len(sources)==65
        return endpoint+'Complete',66,sources
    sources[root+'Complete']=wrapper(group,old_ns,index)
    assert len(sources)==154
    return root+'Complete',154,sources
def fallback(group,half,packet):
    assert group in [805,806,807] and half in [0,1]
    ns=f'D3OriginalFallbackGroup{group:04d}';sources={};leaves=[];deps=[]
    for index in range(4*group+2*half,4*group+2*half+2):
        key=f'Proofs.RadenkovicGutmanFixedDegree03Class00Depth1PrunedControlLeaf{index:04d}'
        cell=packet['leaves'][key];root='Proofs.RadenkovicGutman'+ns+f'Leaf{index:05d}'
        sources.update(cell_sources(index,cell,root,ns));leaves.append(f'leaf{index:05d}');deps.append(root)
    endpoint='Proofs.RadenkovicGutman'+ns+f'Half{half}'
    sources[endpoint]='/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/\n'+''.join('import '+n+'\n' for n in deps)+f'''namespace Gebendorfer.RadenkovicGutman.{ns}
theorem half{half}_checked : FastNestedCellData.accepts 3 4 4 {leaves[0]}=true ∧
    FastNestedCellData.accepts 3 4 4 {leaves[1]}=true :=
  ⟨{leaves[0]}_checked,{leaves[1]}_checked⟩
#print axioms half{half}_checked
end Gebendorfer.RadenkovicGutman.{ns}
'''
    assert len(sources)==307
    return endpoint,308,sources
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--endpoint',required=True);a=ap.parse_args()
    match=re.fullmatch(r'Proofs\.RadenkovicGutmanD3(?:PowerParameterGroup|FullParameterGroup)(\d{4})Complete',a.endpoint)
    fb=re.fullmatch(r'Proofs\.RadenkovicGutmanD3OriginalFallbackGroup(\d{4})Half([01])',a.endpoint)
    assert match or fb
    group=int((match or fb)[1]);part=group//238
    registry=json.loads((R/f'ci/rg_d3_refined_original_square_part{part}_registry.json').read_bytes())
    assert a.endpoint in registry['endpoints']
    for row in registry['source_inputs']:
        assert hashlib.sha256((R/row['path']).read_bytes()).hexdigest()==row['sha256'],row['path']
    report,packet=inputs()
    endpoint,maximum,sources=full(group,report) if match else fallback(group,int(fb[2]),packet)
    assert endpoint==a.endpoint and maximum==registry['endpoints'][endpoint]['max_fresh']
    assert shutil.disk_usage(R).free>8*1024**3+16*1024**2
    total=0;hashes={};bundle=S/'build/fresh_exports/generated_source'
    for name,text in sources.items():
        raw=text.encode();total+=len(raw);digest=hashlib.sha256(raw).hexdigest()
        assert digest==registry['sources'][name],name
        rel='Proofs/RG_Lean_20261019/'+name.replace('.','/')+'.lean';dest=R/rel
        if dest.exists():assert dest.read_bytes()==raw,name
        else:dest.write_bytes(raw)
        target=bundle/rel;target.parent.mkdir(parents=True,exist_ok=True)
        if target.exists():assert target.read_bytes()==raw
        else:target.write_bytes(raw)
        hashes[rel]=digest
    assert total<16*1024**2
    (bundle/'generated_source_manifest.json').write_bytes((json.dumps(dict(endpoint=endpoint,original_group=group,original_class_indices=[4,4],original_recipe_sha256=report['original_recipe_sha256'],source_sha256=hashes,kind='CANDIDATES_REQUIRE_SUCCESSFUL_KERNEL_RECEIPT'),indent=2)+'\n').encode())
    print(json.dumps(dict(status='ORIGINAL_INTERVAL_PAYMENT_PROOFS_REQUIRE_KERNEL',endpoint=endpoint,group=group,modules=len(sources),source_bytes=total,distinct_coverage_added=0,whole_class='OPEN',universal_rg='OPEN')),flush=True)
if __name__=='__main__':main()
