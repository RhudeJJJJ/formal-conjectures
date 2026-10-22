/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01258 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 4372542302587373274703855616000000000000 4671680904460278309217269035417550716928 1231796287991611427247051767808000000000000))
theorem leaf01258_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 4372542302587373274703855616000000000000 4671680904460278309217269035417550716928 1231796287991611427247051767808000000000000 raw01258=true := by decide +kernel
#print axioms leaf01258_raw
theorem leaf01258_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01258=true := by decide +kernel
#print axioms leaf01258_rectangular
def affine01258 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01258 (IntegerComputedClassCell.leftNumerator ![(13/64),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/64),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/64),0,(7/8)] ![(1/128),1,(1/16)]))
theorem leaf01258_transform : affine01258=(NestedInteger.clearedAll 3 raw01258 (IntegerComputedClassCell.leftNumerator ![(13/64),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/64),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/64),0,(7/8)] ![(1/128),1,(1/16)])) := by decide +kernel
#print axioms leaf01258_transform
theorem leaf01258_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01258=true := by decide +kernel
#print axioms leaf01258_sign
theorem leaf01258_log : RationalLog.accepts (1142865287/1073741824) (66989613/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01258_log
def leaf01258 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (3792575891/1000000000000) (1142865287/1073741824) (66989613/2147483648) 0 8 ![60,0,4] ![(13/64),0,(7/8)] ![(1/128),1,(1/16)] affine01258
theorem leaf01258_checked : FastNestedCellData.accepts 1 2 4 leaf01258=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (3792575891/1000000000000) (1142865287/1073741824) (66989613/2147483648) 0 8 ![60,0,4] ![(13/64),0,(7/8)] ![(1/128),1,(1/16)] 4372542302587373274703855616000000000000 4671680904460278309217269035417550716928 1231796287991611427247051767808000000000000 raw01258 affine01258
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01258_raw leaf01258_rectangular
    leaf01258_transform leaf01258_sign leaf01258_log
#print axioms leaf01258_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
