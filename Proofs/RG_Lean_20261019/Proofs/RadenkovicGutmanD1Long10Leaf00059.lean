/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00059 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 429250658549314271225873170432000000000000 405626622989894141886493322884654949203968 17431517820066490891404872515584000000000000))
theorem leaf00059_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 429250658549314271225873170432000000000000 405626622989894141886493322884654949203968 17431517820066490891404872515584000000000000 raw00059=true := by decide +kernel
#print axioms leaf00059_raw
theorem leaf00059_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00059=true := by decide +kernel
#print axioms leaf00059_rectangular
def affine00059 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00059 (IntegerComputedClassCell.leftNumerator ![(1/160),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/160),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/160),0,(1/2)] ![(1/3200),1,(1/2)]))
theorem leaf00059_transform : affine00059=(NestedInteger.clearedAll 3 raw00059 (IntegerComputedClassCell.leftNumerator ![(1/160),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/160),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/160),0,(1/2)] ![(1/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00059_transform
theorem leaf00059_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00059=true := by decide +kernel
#print axioms leaf00059_sign
theorem leaf00059_log : RationalLog.accepts (3966296877/4294967296) (-85481741/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00059_log
def leaf00059 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (23269724827/1000000000000) (3966296877/4294967296) (-85481741/2147483648) 1 8 ![52,0,4] ![(1/160),0,(1/2)] ![(1/3200),1,(1/2)] affine00059
theorem leaf00059_checked : FastNestedCellData.accepts 1 0 4 leaf00059=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (23269724827/1000000000000) (3966296877/4294967296) (-85481741/2147483648) 1 8 ![52,0,4] ![(1/160),0,(1/2)] ![(1/3200),1,(1/2)] 429250658549314271225873170432000000000000 405626622989894141886493322884654949203968 17431517820066490891404872515584000000000000 raw00059 affine00059
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00059_raw leaf00059_rectangular
    leaf00059_transform leaf00059_sign leaf00059_log
#print axioms leaf00059_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
