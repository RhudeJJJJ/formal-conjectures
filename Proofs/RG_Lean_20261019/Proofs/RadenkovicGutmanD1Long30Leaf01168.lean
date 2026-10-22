/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01168 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 3325172340192115096590850457600000000000 4218107342999082518661733330462781210624 73126234777393804202435674112000000000000))
theorem leaf01168_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 3325172340192115096590850457600000000000 4218107342999082518661733330462781210624 73126234777393804202435674112000000000000 raw01168=true := by decide +kernel
#print axioms leaf01168_raw
theorem leaf01168_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01168=true := by decide +kernel
#print axioms leaf01168_rectangular
def affine01168 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01168 (IntegerComputedClassCell.leftNumerator ![(5/8),0,(7/8)] ![(1/8),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(5/8),0,(7/8)] ![(1/8),1,(1/16)]) (IntegerComputedClassCell.denominator ![(5/8),0,(7/8)] ![(1/8),1,(1/16)]))
theorem leaf01168_transform : affine01168=(NestedInteger.clearedAll 3 raw01168 (IntegerComputedClassCell.leftNumerator ![(5/8),0,(7/8)] ![(1/8),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(5/8),0,(7/8)] ![(1/8),1,(1/16)]) (IntegerComputedClassCell.denominator ![(5/8),0,(7/8)] ![(1/8),1,(1/16)])) := by decide +kernel
#print axioms leaf01168_transform
theorem leaf01168_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01168=true := by decide +kernel
#print axioms leaf01168_sign
theorem leaf01168_log : RationalLog.accepts (1287798755/1073741824) (195189931/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01168_log
def leaf01168 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (28841272601/500000000000) (1287798755/1073741824) (195189931/2147483648) 0 8 ![60,0,4] ![(5/8),0,(7/8)] ![(1/8),1,(1/16)] affine01168
theorem leaf01168_checked : FastNestedCellData.accepts 1 2 4 leaf01168=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (28841272601/500000000000) (1287798755/1073741824) (195189931/2147483648) 0 8 ![60,0,4] ![(5/8),0,(7/8)] ![(1/8),1,(1/16)] 3325172340192115096590850457600000000000 4218107342999082518661733330462781210624 73126234777393804202435674112000000000000 raw01168 affine01168
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01168_raw leaf01168_rectangular
    leaf01168_transform leaf01168_sign leaf01168_log
#print axioms leaf01168_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
