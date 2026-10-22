/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01304 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 342775955496407872659521536000000000000 353807758249758872761084037825367638016 297506699669284638023340785664000000000000))
theorem leaf01304_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 342775955496407872659521536000000000000 353807758249758872761084037825367638016 297506699669284638023340785664000000000000 raw01304=true := by decide +kernel
#print axioms leaf01304_raw
theorem leaf01304_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01304=true := by decide +kernel
#print axioms leaf01304_rectangular
def affine01304 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01304 (IntegerComputedClassCell.leftNumerator ![(17/128),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/128),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/128),0,(15/16)] ![(1/128),1,(1/16)]))
theorem leaf01304_transform : affine01304=(NestedInteger.clearedAll 3 raw01304 (IntegerComputedClassCell.leftNumerator ![(17/128),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/128),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/128),0,(15/16)] ![(1/128),1,(1/16)])) := by decide +kernel
#print axioms leaf01304_transform
theorem leaf01304_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01304=true := by decide +kernel
#print axioms leaf01304_sign
theorem leaf01304_log : RationalLog.accepts (1106982351/1073741824) (32736381/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01304_log
def leaf01304 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (594621497/500000000000) (1106982351/1073741824) (32736381/2147483648) 0 8 ![60,0,4] ![(17/128),0,(15/16)] ![(1/128),1,(1/16)] affine01304
theorem leaf01304_checked : FastNestedCellData.accepts 1 2 4 leaf01304=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (594621497/500000000000) (1106982351/1073741824) (32736381/2147483648) 0 8 ![60,0,4] ![(17/128),0,(15/16)] ![(1/128),1,(1/16)] 342775955496407872659521536000000000000 353807758249758872761084037825367638016 297506699669284638023340785664000000000000 raw01304 affine01304
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01304_raw leaf01304_rectangular
    leaf01304_transform leaf01304_sign leaf01304_log
#print axioms leaf01304_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
