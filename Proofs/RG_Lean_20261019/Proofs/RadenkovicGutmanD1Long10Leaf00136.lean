/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00136 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 2352374801586277954239755976704000000000000 1770482393482976197170205676408224251641856 13883687062778349319035367194624000000000000))
theorem leaf00136_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 2352374801586277954239755976704000000000000 1770482393482976197170205676408224251641856 13883687062778349319035367194624000000000000 raw00136=true := by decide +kernel
#print axioms leaf00136_raw
theorem leaf00136_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00136=true := by decide +kernel
#print axioms leaf00136_rectangular
def affine00136 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00136 (IntegerComputedClassCell.leftNumerator ![(27/1600),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(27/1600),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(27/1600),0,(1/4)] ![(1/1600),1,(1/4)]))
theorem leaf00136_transform : affine00136=(NestedInteger.clearedAll 3 raw00136 (IntegerComputedClassCell.leftNumerator ![(27/1600),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(27/1600),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(27/1600),0,(1/4)] ![(1/1600),1,(1/4)])) := by decide +kernel
#print axioms leaf00136_transform
theorem leaf00136_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00136=true := by decide +kernel
#print axioms leaf00136_sign
theorem leaf00136_log : RationalLog.accepts (2866947501/4294967296) (-868004477/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00136_log
def leaf00136 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (127522493519/1000000000000) (2866947501/4294967296) (-868004477/4294967296) 1 8 ![52,0,4] ![(27/1600),0,(1/4)] ![(1/1600),1,(1/4)] affine00136
theorem leaf00136_checked : FastNestedCellData.accepts 1 0 4 leaf00136=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (127522493519/1000000000000) (2866947501/4294967296) (-868004477/4294967296) 1 8 ![52,0,4] ![(27/1600),0,(1/4)] ![(1/1600),1,(1/4)] 2352374801586277954239755976704000000000000 1770482393482976197170205676408224251641856 13883687062778349319035367194624000000000000 raw00136 affine00136
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00136_raw leaf00136_rectangular
    leaf00136_transform leaf00136_sign leaf00136_log
#print axioms leaf00136_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
