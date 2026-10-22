/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00142 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 709973217478649226398688870400000000000 633411854936955996537663003685344509952 12857424245930982561583988736000000000000))
theorem leaf00142_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 709973217478649226398688870400000000000 633411854936955996537663003685344509952 12857424245930982561583988736000000000000 raw00142=true := by decide +kernel
#print axioms leaf00142_raw
theorem leaf00142_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00142=true := by decide +kernel
#print axioms leaf00142_rectangular
def affine00142 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00142 (IntegerComputedClassCell.leftNumerator ![(1/320),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(1/320),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(1/320),0,(1/8)] ![(3/32000),1,(1/8)]))
theorem leaf00142_transform : affine00142=(NestedInteger.clearedAll 3 raw00142 (IntegerComputedClassCell.leftNumerator ![(1/320),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(1/320),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(1/320),0,(1/8)] ![(3/32000),1,(1/8)])) := by decide +kernel
#print axioms leaf00142_transform
theorem leaf00142_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00142=true := by decide +kernel
#print axioms leaf00142_sign
theorem leaf00142_log : RationalLog.accepts (228243915/268435456) (-87078129/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00142_log
def leaf00142 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (49264288307/1000000000000) (228243915/268435456) (-87078129/1073741824) 1 8 ![60,0,4] ![(1/320),0,(1/8)] ![(3/32000),1,(1/8)] affine00142
theorem leaf00142_checked : FastNestedCellData.accepts 1 2 4 leaf00142=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (49264288307/1000000000000) (228243915/268435456) (-87078129/1073741824) 1 8 ![60,0,4] ![(1/320),0,(1/8)] ![(3/32000),1,(1/8)] 709973217478649226398688870400000000000 633411854936955996537663003685344509952 12857424245930982561583988736000000000000 raw00142 affine00142
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00142_raw leaf00142_rectangular
    leaf00142_transform leaf00142_sign leaf00142_log
#print axioms leaf00142_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
