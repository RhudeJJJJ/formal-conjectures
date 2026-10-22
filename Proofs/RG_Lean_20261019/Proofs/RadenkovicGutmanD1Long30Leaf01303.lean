/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01303 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 342775955496407872659521536000000000000 353807758249758872761084037825367638016 297506699669284638023340785664000000000000))
theorem leaf01303_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 342775955496407872659521536000000000000 353807758249758872761084037825367638016 297506699669284638023340785664000000000000 raw01303=true := by decide +kernel
#print axioms leaf01303_raw
theorem leaf01303_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01303=true := by decide +kernel
#print axioms leaf01303_rectangular
def affine01303 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01303 (IntegerComputedClassCell.leftNumerator ![(17/128),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/128),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/128),0,(7/8)] ![(1/128),1,(1/16)]))
theorem leaf01303_transform : affine01303=(NestedInteger.clearedAll 3 raw01303 (IntegerComputedClassCell.leftNumerator ![(17/128),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/128),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/128),0,(7/8)] ![(1/128),1,(1/16)])) := by decide +kernel
#print axioms leaf01303_transform
theorem leaf01303_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01303=true := by decide +kernel
#print axioms leaf01303_sign
theorem leaf01303_log : RationalLog.accepts (1106982351/1073741824) (32736381/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01303_log
def leaf01303 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (594621497/500000000000) (1106982351/1073741824) (32736381/2147483648) 0 8 ![60,0,4] ![(17/128),0,(7/8)] ![(1/128),1,(1/16)] affine01303
theorem leaf01303_checked : FastNestedCellData.accepts 1 2 4 leaf01303=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (594621497/500000000000) (1106982351/1073741824) (32736381/2147483648) 0 8 ![60,0,4] ![(17/128),0,(7/8)] ![(1/128),1,(1/16)] 342775955496407872659521536000000000000 353807758249758872761084037825367638016 297506699669284638023340785664000000000000 raw01303 affine01303
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01303_raw leaf01303_rectangular
    leaf01303_transform leaf01303_sign leaf01303_log
#print axioms leaf01303_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
