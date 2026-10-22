/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00396 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 57544360845056449174499753984000000000000 76916506850629115656495453956714390355968 385262315477383690093212991488000000000000))
theorem leaf00396_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 57544360845056449174499753984000000000000 76916506850629115656495453956714390355968 385262315477383690093212991488000000000000 raw00396=true := by decide +kernel
#print axioms leaf00396_raw
theorem leaf00396_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00396=true := by decide +kernel
#print axioms leaf00396_rectangular
def affine00396 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00396 (IntegerComputedClassCell.leftNumerator ![(11/16),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/16),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/16),0,0] ![(1/16),1,(1/2)]))
theorem leaf00396_transform : affine00396=(NestedInteger.clearedAll 3 raw00396 (IntegerComputedClassCell.leftNumerator ![(11/16),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/16),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/16),0,0] ![(1/16),1,(1/2)])) := by decide +kernel
#print axioms leaf00396_transform
theorem leaf00396_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00396=true := by decide +kernel
#print axioms leaf00396_sign
theorem leaf00396_log : RationalLog.accepts (4785453847/4294967296) (232222283/4294967296) 0 8=true := by decide +kernel
#print axioms leaf00396_log
def leaf00396 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (24955888417/125000000000) (4785453847/4294967296) (232222283/4294967296) 0 8 ![52,0,4] ![(11/16),0,0] ![(1/16),1,(1/2)] affine00396
theorem leaf00396_checked : FastNestedCellData.accepts 1 0 4 leaf00396=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (24955888417/125000000000) (4785453847/4294967296) (232222283/4294967296) 0 8 ![52,0,4] ![(11/16),0,0] ![(1/16),1,(1/2)] 57544360845056449174499753984000000000000 76916506850629115656495453956714390355968 385262315477383690093212991488000000000000 raw00396 affine00396
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00396_raw leaf00396_rectangular
    leaf00396_transform leaf00396_sign leaf00396_log
#print axioms leaf00396_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
