/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00246 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 2991193905146283082778597654528000000000000 163340857395979918921339763188821783478272 251831466691272127638977642496000000000000))
theorem leaf00246_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 2991193905146283082778597654528000000000000 163340857395979918921339763188821783478272 251831466691272127638977642496000000000000 raw00246=true := by decide +kernel
#print axioms leaf00246_raw
theorem leaf00246_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00246=true := by decide +kernel
#print axioms leaf00246_rectangular
def affine00246 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00246 (IntegerComputedClassCell.leftNumerator ![(151/3200),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(151/3200),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(151/3200),0,0] ![(3/3200),1,(1/4)]))
theorem leaf00246_transform : affine00246=(NestedInteger.clearedAll 3 raw00246 (IntegerComputedClassCell.leftNumerator ![(151/3200),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(151/3200),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(151/3200),0,0] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00246_transform
theorem leaf00246_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00246=true := by decide +kernel
#print axioms leaf00246_sign
theorem leaf00246_log : RationalLog.accepts (71131461/2147483648) (-1829399655/1073741824) 5 8=true := by decide +kernel
#print axioms leaf00246_log
def leaf00246 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (648611786057/1000000000000) (71131461/2147483648) (-1829399655/1073741824) 5 8 ![52,0,4] ![(151/3200),0,0] ![(3/3200),1,(1/4)] affine00246
theorem leaf00246_checked : FastNestedCellData.accepts 1 0 4 leaf00246=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (648611786057/1000000000000) (71131461/2147483648) (-1829399655/1073741824) 5 8 ![52,0,4] ![(151/3200),0,0] ![(3/3200),1,(1/4)] 2991193905146283082778597654528000000000000 163340857395979918921339763188821783478272 251831466691272127638977642496000000000000 raw00246 affine00246
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00246_raw leaf00246_rectangular
    leaf00246_transform leaf00246_sign leaf00246_log
#print axioms leaf00246_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
