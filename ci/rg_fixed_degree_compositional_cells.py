"""Compose the already checked integer-cell method at a concrete root degree.

This proposes ordinary Lean source. Every arithmetic identity and acceptance
predicate remains a kernel obligation; physical degree and polynomial dimension
are kept distinct.
"""
import pathlib,re
from fractions import Fraction as Q
from rg_compositional_d1_repair import build as original_build
R=pathlib.Path(__file__).resolve().parent.parent
S=R/'Proofs/RG_Lean_20261019'
def norm_names(degree):
    assert 1<=degree<=45
    if degree==1:return ('DegreeOneNormPack00','DegreeOneIntegerNorm00','RadenkovicGutmanD1IntegerNorm00')
    if degree==3:return ('FixedDegree03Long00StagedNormPack','FixedDegree03Long00StagedIntegerNorm','RadenkovicGutmanD3Long00StagedIntegerNorm')
    stem=f'FixedDegree{degree:02d}Long00Compositional'
    return (stem+'NormPack',stem+'IntegerNorm',f'RadenkovicGutmanD{degree}Long00CompositionalIntegerNorm')
def rat(value):
    q=Q(value)
    return str(q.numerator) if q.denominator==1 else f'({q.numerator}/{q.denominator})'
def cell_sources(degree,index,cell,root,namespace):
    norm,integer,module=norm_names(degree)
    old=f'Proofs.RadenkovicGutmanD1Long00Leaf{index:05d}CompositionalRepair'
    result={}
    for name,text in original_build(index,cell).items():
        text=text.replace(old,root).replace('DegreeOneLongClass00',namespace)
        text=text.replace('DegreeOneIntegerNorm00.pack',integer+'.pack').replace('DegreeOneNormPack00.pack',norm+'.pack')
        text=text.replace('import Proofs.RadenkovicGutmanD1IntegerNorm00','import Proofs.'+module)
        if name==old:
            assert text.count('FastNestedCellData.accepts 1 4 4')==1
            text=text.replace('FastNestedCellData.accepts 1 4 4',f'FastNestedCellData.accepts {degree} 4 4')
        result[name.replace(old,root)]=text
    assert len(result)==153
    return result
def power_sources(index,sources,old_root,old_namespace,new_root,new_namespace):
    tail=sources[old_root];tail=tail[tail.index(f'theorem leaf{index:05d}_log :'):]
    tail=tail.replace('end Gebendorfer.RadenkovicGutman.'+old_namespace,'end Gebendorfer.RadenkovicGutman.'+new_namespace)
    text=f'''/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import {old_root}AffineLength
import Proofs.RadenkovicGutmanPowerBernstein
namespace Gebendorfer.RadenkovicGutman.{new_namespace}
open {old_namespace}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem leaf{index:05d}_sign : NestedInteger.bernsteinCheck 3 ![88,4,4] leaf{index:05d}_w_affine=true :=
  PowerBernstein.checked 3 ![88,4,4] leaf{index:05d}_w_affine
    (by decide +kernel) (by decide +kernel)
#print axioms leaf{index:05d}_sign
'''+tail
    result={n:t for n,t in sources.items() if n!=old_root and not re.fullmatch(re.escape(old_root)+r'Row\d{3}',n)}
    assert len(result)==63
    result[new_root]=text
    return result
def slice_wrapper(degree,index,namespace,left,right,payment):
    text=(R/'ci/rg_d3_original_square_wrapper.lean.txt').read_text()
    line=next(l for l in text.splitlines() if l.startswith('theorem cover_checked :'))
    match=re.fullmatch(r'theorem cover_checked : FastArmCover.accepts 3 4 4 (\S+) (\S+) 0 1 0 1 (\S+) cover=true := by',line);assert match
    for old,new in zip(match.groups(),[left,right,payment]):text=text.replace(old,rat(new))
    text=text.replace('D3FullParameterGroup0000',namespace).replace('leaf00000',f'leaf{index:05d}')
    for before,after in [
        ('FastArmCover.accepts 3 4 4',f'FastArmCover.accepts {degree} 4 4'),
        ('FastArmCoverIntegral.accepts 3 4 4',f'FastArmCoverIntegral.accepts {degree} 4 4'),
        ('FastArmCoverIntegral.accepts_of_checks 3 4 4',f'FastArmCoverIntegral.accepts_of_checks {degree} 4 4'),
        ('(hd : C.degree u=3)',f'(hd : C.degree u={degree})'),
        ('FastArmCoverIntegral.single_integral_lower C u p q 3 (by decide)',f'FastArmCoverIntegral.single_integral_lower C u p q {degree} (by decide)')]:
        assert text.count(before)==1,before
        text=text.replace(before,after)
    return text
def integer_norm_source(degree):
    norm,integer,module=norm_names(degree)
    assert degree not in [1,3]
    source=(S/'Proofs/RadenkovicGutmanD3Long00StagedIntegerNorm.lean').read_text()
    source=source.replace('RadenkovicGutmanD3Long00StagedNormPack',f'RadenkovicGutmanD{degree}Long00CompositionalNormPack')
    source=source.replace('FixedDegree03Long00StagedNormPack',norm).replace('FixedDegree03Long00StagedIntegerNorm',integer)
    return 'Proofs.'+module,source
