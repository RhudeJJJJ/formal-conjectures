/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01333 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 1012509681988925272065310720000000000 1026810112935070886462778571654955008 2923012691654382177187004416000000000000))
theorem leaf01333_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 1012509681988925272065310720000000000 1026810112935070886462778571654955008 2923012691654382177187004416000000000000 raw01333=true := by decide +kernel
#print axioms leaf01333_raw
theorem leaf01333_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01333=true := by decide +kernel
#print axioms leaf01333_rectangular
def affine01333 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01333 (IntegerComputedClassCell.leftNumerator ![(11/128),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/128),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/128),0,(7/8)] ![(1/128),1,(1/16)]))
theorem leaf01333_transform : affine01333=(NestedInteger.clearedAll 3 raw01333 (IntegerComputedClassCell.leftNumerator ![(11/128),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/128),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/128),0,(7/8)] ![(1/128),1,(1/16)])) := by decide +kernel
#print axioms leaf01333_transform
theorem leaf01333_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01333=true := by decide +kernel
#print axioms leaf01333_sign
theorem leaf01333_log : RationalLog.accepts (272131175/268435456) (29364075/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01333_log
def leaf01333 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (351284863/1000000000000) (272131175/268435456) (29364075/4294967296) 0 8 ![60,0,4] ![(11/128),0,(7/8)] ![(1/128),1,(1/16)] affine01333
theorem leaf01333_checked : FastNestedCellData.accepts 1 2 4 leaf01333=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (351284863/1000000000000) (272131175/268435456) (29364075/4294967296) 0 8 ![60,0,4] ![(11/128),0,(7/8)] ![(1/128),1,(1/16)] 1012509681988925272065310720000000000 1026810112935070886462778571654955008 2923012691654382177187004416000000000000 raw01333 affine01333
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01333_raw leaf01333_rectangular
    leaf01333_transform leaf01333_sign leaf01333_log
#print axioms leaf01333_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
