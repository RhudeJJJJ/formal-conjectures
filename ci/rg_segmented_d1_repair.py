"""Same pinned original cells, using the successful noncomputable segmented proof."""
import argparse,hashlib,json,pathlib,re,shutil
from rg_segmented_d1_repair_body import body
R=pathlib.Path(__file__).resolve().parent.parent;S=R/'Proofs/RG_Lean_20261019'
PACKET_SHA='cce5075dc04b2b8250c6945e24047682a73335f5947cc612ce337453b075eaf0'

def packet_leaves():
    raw=(R/'ci/rg_d1_shared_packet00.json').read_bytes();assert hashlib.sha256(raw).hexdigest()==PACKET_SHA
    data=json.loads(raw);leaves=[]
    def walk(t):
        if t['kind'] in ['first','second']:walk(t['left']);walk(t['right'])
        else:assert t['kind']=='polynomial';leaves.append(t)
    for c in data['cells']:walk(c['tree'])
    assert len(leaves)==1754
    return leaves

def build(index,cell):
    assert cell['degrees']==[88,4,4]
    imports,text=body('00',index,cell,shared_weights=True,outer_chunk=3)
    stem=f'leaf{index:05d}_w_';root=f'Proofs.RadenkovicGutmanD1Long00Leaf{index:05d}Repair';sources={}
    def module(n,deps,content):
        header='/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/\n'+''.join('import '+d+'\n' for d in deps)
        header+='import Proofs.RadenkovicGutmanClosedIntegerRowElaboration\nnamespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\nopen NestedInteger NestedHorner\n'
        content=re.sub(r'^open NestedInteger NestedHorner\n','',content,count=1)
        content=re.sub(r'^def ','noncomputable def ',content,flags=re.M)
        content=content.replace('rg_integer_data%','rg_closed_integer_data%').replace('rg_integer_row%','rg_closed_integer_row%')
        sources[n]=header+content+'end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00\n'
    end=text.index(f'def {stem}source00 :');module(root+'Prepared',imports,text[:end])
    aliases=''
    for i in range(30):
        start=text.index(f'def {stem}source{i:02d} :');end=text.index(f'def {stem}weights{i:02d} :',start)
        aliases+=text[start:end]
    module(root+'Sources',[root+'Prepared'],aliases+f'#print axioms leaf{index:05d}_inner\n')
    for i in range(30):
        start=text.index(f'def {stem}weights{i:02d} :')
        end=text.index(f'def {stem}source{i+1:02d} :',start) if i<29 else text.index(f'def {stem}suffix29 :',start)
        module(root+f'Piece{i:02d}',[root+'Sources'],text[start:end])
    for i in reversed(range(30)):
        name='affine' if i==0 else f'suffix{i:02d}';start=text.index(f'def {stem}{name} :')
        if i>0:
            next_name='affine' if i==1 else f'suffix{i-1:02d}';end=text.index(f'def {stem}{next_name} :',start)
        else:end=text.index(f'theorem {stem}affine_length :',start)
        module(root+f'Join{i:02d}',[root+f'Piece{i:02d}']+([root+f'Join{i+1:02d}'] if i<29 else []),text[start:end])
    start=text.index(f'theorem {stem}affine_length :');end=text.index(f'def {stem}row000 :',start)
    module(root+'AffineLength',[root+'Join00'],text[start:end])
    rows=[]
    for i in range(89):
        start=text.index(f'def {stem}row{i:03d} :')
        end=text.index(f'def {stem}row{i+1:03d} :',start) if i<88 else text.index(f'def {stem}rows :',start)
        ep=root+f'Row{i:03d}';rows.append(ep);module(ep,[root+'AffineLength'],text[start:end])
    tail=text[text.index(f'def {stem}rows :'):]
    _,original=body('00',index,cell,shared_weights=True,outer_chunk=12)
    marker=f'def leaf{index:05d} :'
    assert tail[tail.index(marker):]==original[original.index(marker):]
    module(root,rows,tail);assert len(sources)==153
    return sources

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--endpoint',required=True);a=ap.parse_args()
    match=re.fullmatch(r'Proofs\.RadenkovicGutmanD1Long00Leaf(\d{5})Repair',a.endpoint);assert match
    index=int(match[1]);manifest=json.loads((R/'ci/rg_d1_segmented_repair_source_registry.json').read_bytes())
    assert index in manifest['indices'] and manifest['packet_sha256']==PACKET_SHA
    assert shutil.disk_usage(R).free>8*1024**3+16*1024**2
    sources=build(index,packet_leaves()[index]);expected=manifest['sources'];size=0
    for n,text in sources.items():
        raw=text.encode();assert hashlib.sha256(raw).hexdigest()==expected[n],n;size+=len(raw)
        path=S/(n.replace('.','/')+'.lean')
        if path.exists():assert path.read_bytes()==raw,n
        else:path.write_bytes(raw)
    assert size<16*1024**2
    print(json.dumps(dict(status='PINNED_ORIGINAL_CELL_SEGMENTED_SOURCES_REQUIRE_KERNEL',index=index,modules=len(sources),bytes=size,mathematical_coverage_added=0)),flush=True)
if __name__=='__main__':main()
