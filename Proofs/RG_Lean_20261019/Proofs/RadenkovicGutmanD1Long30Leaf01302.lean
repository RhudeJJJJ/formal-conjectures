/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01302 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 342775955496407872659521536000000000000 353807758249758872761084037825367638016 297506699669284638023340785664000000000000))
theorem leaf01302_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 342775955496407872659521536000000000000 353807758249758872761084037825367638016 297506699669284638023340785664000000000000 raw01302=true := by decide +kernel
#print axioms leaf01302_raw
theorem leaf01302_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01302=true := by decide +kernel
#print axioms leaf01302_rectangular
def affine01302 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01302 (IntegerComputedClassCell.leftNumerator ![(17/128),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(17/128),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.denominator ![(17/128),0,(3/4)] ![(1/128),1,(1/8)]))
theorem leaf01302_transform : affine01302=(NestedInteger.clearedAll 3 raw01302 (IntegerComputedClassCell.leftNumerator ![(17/128),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(17/128),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.denominator ![(17/128),0,(3/4)] ![(1/128),1,(1/8)])) := by decide +kernel
#print axioms leaf01302_transform
theorem leaf01302_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01302=true := by decide +kernel
#print axioms leaf01302_sign
theorem leaf01302_log : RationalLog.accepts (1106982351/1073741824) (32736381/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01302_log
def leaf01302 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (594621497/500000000000) (1106982351/1073741824) (32736381/2147483648) 0 8 ![60,0,4] ![(17/128),0,(3/4)] ![(1/128),1,(1/8)] affine01302
theorem leaf01302_checked : FastNestedCellData.accepts 1 2 4 leaf01302=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (594621497/500000000000) (1106982351/1073741824) (32736381/2147483648) 0 8 ![60,0,4] ![(17/128),0,(3/4)] ![(1/128),1,(1/8)] 342775955496407872659521536000000000000 353807758249758872761084037825367638016 297506699669284638023340785664000000000000 raw01302 affine01302
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01302_raw leaf01302_rectangular
    leaf01302_transform leaf01302_sign leaf01302_log
#print axioms leaf01302_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
