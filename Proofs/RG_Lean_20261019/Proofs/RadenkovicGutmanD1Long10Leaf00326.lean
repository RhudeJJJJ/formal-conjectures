/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00326 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 21980895789113538716402450432000000000000 14348257414195872273978607564665133203456 47036340912724543918716223488000000000000))
theorem leaf00326_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 21980895789113538716402450432000000000000 14348257414195872273978607564665133203456 47036340912724543918716223488000000000000 raw00326=true := by decide +kernel
#print axioms leaf00326_raw
theorem leaf00326_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00326=true := by decide +kernel
#print axioms leaf00326_rectangular
def affine00326 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00326 (IntegerComputedClassCell.leftNumerator ![(17/160),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(17/160),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(17/160),0,(1/2)] ![(1/160),1,(1/2)]))
theorem leaf00326_transform : affine00326=(NestedInteger.clearedAll 3 raw00326 (IntegerComputedClassCell.leftNumerator ![(17/160),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(17/160),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(17/160),0,(1/2)] ![(1/160),1,(1/2)])) := by decide +kernel
#print axioms leaf00326_transform
theorem leaf00326_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00326=true := by decide +kernel
#print axioms leaf00326_sign
theorem leaf00326_log : RationalLog.accepts (134266529/268435456) (-743870799/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00326_log
def leaf00326 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (305046207587/1000000000000) (134266529/268435456) (-743870799/2147483648) 1 8 ![52,0,4] ![(17/160),0,(1/2)] ![(1/160),1,(1/2)] affine00326
theorem leaf00326_checked : FastNestedCellData.accepts 1 0 4 leaf00326=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (305046207587/1000000000000) (134266529/268435456) (-743870799/2147483648) 1 8 ![52,0,4] ![(17/160),0,(1/2)] ![(1/160),1,(1/2)] 21980895789113538716402450432000000000000 14348257414195872273978607564665133203456 47036340912724543918716223488000000000000 raw00326 affine00326
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00326_raw leaf00326_rectangular
    leaf00326_transform leaf00326_sign leaf00326_log
#print axioms leaf00326_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
