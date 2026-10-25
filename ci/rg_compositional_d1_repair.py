"""Keep all original certificate data; compose evaluated suffixes generically."""
import argparse,hashlib,json,math,pathlib,re,shutil
from fractions import Fraction as Q
from rg_segmented_d1_repair import build as original_build,packet_leaves,PACKET_SHA
R=pathlib.Path(__file__).resolve().parent.parent;S=R/'Proofs/RG_Lean_20261019'
def build(index,cell):
    old=original_build(index,cell);prefix=f'Proofs.RadenkovicGutmanD1Long00Leaf{index:05d}Repair'
    root=prefix.replace('Repair','CompositionalRepair');mapping={n:n.replace(prefix,root) for n in old};result={};stem=f'leaf{index:05d}_w_'
    left,width=Q(cell['box_left'][0]),Q(cell['box_width'][0]);den=math.lcm(left.denominator,width.denominator);ln,wn=int(left*den),int(width*den)
    for n,before in old.items():
        text=before
        for source,target in mapping.items():text=text.replace('import '+source+'\n','import '+target+'\n')
        match=re.fullmatch(re.escape(prefix)+r'Join(\d{2})',n)
        if match and int(match[1])<29:
            i=int(match[1]);name='affine' if i==0 else f'suffix{i:02d}';marker=f'theorem {stem}{name}_eval (x : Fin 3 → ℝ) :'
            start=text.index(marker);end=text.index('#print axioms',start);declaration=text[start:text.index(':= by',start)]
            following=f'{stem}suffix{i+1:02d}'
            proof=f'''{declaration}:=
  IntegerOuterJoinedEvaluation.joined {ln} {wn} {den} {3*i} {3*i+3}
    {stem}segment{i:02d} {stem}source{i+1:02d} {stem}source{i:02d}
    {stem}piece{i:02d} {following} {stem}{name}
    (by decide +kernel) (List.take_append_drop 3 {stem}source{i:02d})
    {stem}piece{i:02d}_identity {following}_eval {stem}{name}_join x
'''
            text=text[:start]+proof+text[end:]
            text=text.replace('namespace Gebendorfer.', 'import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation\nnamespace Gebendorfer.',1)
        result[mapping[n]]=text
    assert len(result)==153
    # Declaration types, coefficient data, joins, sign and final acceptance are retained.
    root_old=old[prefix];root_new=result[root]
    for source,target in mapping.items():root_new=root_new.replace('import '+target+'\n','import '+source+'\n')
    assert root_new==root_old
    return result
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--endpoint',required=True);a=ap.parse_args()
    m=re.fullmatch(r'Proofs\.RadenkovicGutmanD1Long00Leaf(\d{5})CompositionalRepair',a.endpoint);assert m
    index=int(m[1]);registry=json.loads((R/'ci/rg_compositional_d1_repair_registry.json').read_bytes())
    assert index in registry['indices'] and registry['packet_sha256']==PACKET_SHA
    for row in registry['source_inputs']:assert hashlib.sha256((R/row['path']).read_bytes()).hexdigest()==row['sha256']
    assert shutil.disk_usage(R).free>8*1024**3+16*1024**2
    sources=build(index,packet_leaves()[index]);size=0
    for n,text in sources.items():
        raw=text.encode();assert hashlib.sha256(raw).hexdigest()==registry['sources'][n];size+=len(raw);p=S/(n.replace('.','/')+'.lean')
        if p.exists():assert p.read_bytes()==raw,n
        else:p.write_bytes(raw)
    assert size<16*1024**2
    print(json.dumps(dict(status='SAME_ORIGINAL_CELL_COMPOSITIONAL_REPAIR_REQUIRES_KERNEL',index=index,modules=153,source_bytes=size,mathematical_coverage_added=0)),flush=True)
if __name__=='__main__':main()
