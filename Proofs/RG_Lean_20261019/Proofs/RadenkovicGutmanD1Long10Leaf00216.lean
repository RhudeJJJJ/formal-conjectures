/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00216 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 172613290860314271643701608448000000000000 5821503207306639559282072132072218034176 9720769767191576672183779328000000000000))
theorem leaf00216_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 172613290860314271643701608448000000000000 5821503207306639559282072132072218034176 9720769767191576672183779328000000000000 raw00216=true := by decide +kernel
#print axioms leaf00216_raw
theorem leaf00216_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00216=true := by decide +kernel
#print axioms leaf00216_rectangular
def affine00216 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00216 (IntegerComputedClassCell.leftNumerator ![(121/3200),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(121/3200),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(121/3200),0,0] ![(3/3200),1,(1/4)]))
theorem leaf00216_transform : affine00216=(NestedInteger.clearedAll 3 raw00216 (IntegerComputedClassCell.leftNumerator ![(121/3200),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(121/3200),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(121/3200),0,0] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00216_transform
theorem leaf00216_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00216=true := by decide +kernel
#print axioms leaf00216_sign
theorem leaf00216_log : RationalLog.accepts (22648889/1073741824) (-4143348677/2147483648) 6 8=true := by decide +kernel
#print axioms leaf00216_log
def leaf00216 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (299436327921/500000000000) (22648889/1073741824) (-4143348677/2147483648) 6 8 ![52,0,4] ![(121/3200),0,0] ![(3/3200),1,(1/4)] affine00216
theorem leaf00216_checked : FastNestedCellData.accepts 1 0 4 leaf00216=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (299436327921/500000000000) (22648889/1073741824) (-4143348677/2147483648) 6 8 ![52,0,4] ![(121/3200),0,0] ![(3/3200),1,(1/4)] 172613290860314271643701608448000000000000 5821503207306639559282072132072218034176 9720769767191576672183779328000000000000 raw00216 affine00216
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00216_raw leaf00216_rectangular
    leaf00216_transform leaf00216_sign leaf00216_log
#print axioms leaf00216_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
