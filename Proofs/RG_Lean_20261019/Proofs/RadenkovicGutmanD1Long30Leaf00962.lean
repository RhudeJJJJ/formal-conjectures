/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00962 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 689598970264926422089297035264000000000000 314266532085808284250920015239754817732608 525413549966221827272628764672000000000000))
theorem leaf00962_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 689598970264926422089297035264000000000000 314266532085808284250920015239754817732608 525413549966221827272628764672000000000000 raw00962=true := by decide +kernel
#print axioms leaf00962_raw
theorem leaf00962_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00962=true := by decide +kernel
#print axioms leaf00962_rectangular
def affine00962 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00962 (IntegerComputedClassCell.leftNumerator ![(33/320),0,(1/8)] ![(1/320),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(33/320),0,(1/8)] ![(1/320),1,(1/8)]) (IntegerComputedClassCell.denominator ![(33/320),0,(1/8)] ![(1/320),1,(1/8)]))
theorem leaf00962_transform : affine00962=(NestedInteger.clearedAll 3 raw00962 (IntegerComputedClassCell.leftNumerator ![(33/320),0,(1/8)] ![(1/320),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(33/320),0,(1/8)] ![(1/320),1,(1/8)]) (IntegerComputedClassCell.denominator ![(33/320),0,(1/8)] ![(1/320),1,(1/8)])) := by decide +kernel
#print axioms leaf00962_transform
theorem leaf00962_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00962=true := by decide +kernel
#print axioms leaf00962_sign
theorem leaf00962_log : RationalLog.accepts (1224753833/4294967296) (-84201767/134217728) 2 8=true := by decide +kernel
#print axioms leaf00962_log
def leaf00962 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (149532940341/250000000000) (1224753833/4294967296) (-84201767/134217728) 2 8 ![60,0,4] ![(33/320),0,(1/8)] ![(1/320),1,(1/8)] affine00962
theorem leaf00962_checked : FastNestedCellData.accepts 1 2 4 leaf00962=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (149532940341/250000000000) (1224753833/4294967296) (-84201767/134217728) 2 8 ![60,0,4] ![(33/320),0,(1/8)] ![(1/320),1,(1/8)] 689598970264926422089297035264000000000000 314266532085808284250920015239754817732608 525413549966221827272628764672000000000000 raw00962 affine00962
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00962_raw leaf00962_rectangular
    leaf00962_transform leaf00962_sign leaf00962_log
#print axioms leaf00962_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
