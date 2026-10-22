/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00235 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 337891179910357469696630980608000000000000 192228601565268057671244452535112254357504 655904923602610537997048741888000000000000))
theorem leaf00235_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 337891179910357469696630980608000000000000 192228601565268057671244452535112254357504 655904923602610537997048741888000000000000 raw00235=true := by decide +kernel
#print axioms leaf00235_raw
theorem leaf00235_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00235=true := by decide +kernel
#print axioms leaf00235_rectangular
def affine00235 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00235 (IntegerComputedClassCell.leftNumerator ![(139/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(139/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(139/3200),0,(1/4)] ![(3/3200),1,(1/4)]))
theorem leaf00235_transform : affine00235=(NestedInteger.clearedAll 3 raw00235 (IntegerComputedClassCell.leftNumerator ![(139/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(139/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(139/3200),0,(1/4)] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00235_transform
theorem leaf00235_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00235=true := by decide +kernel
#print axioms leaf00235_sign
theorem leaf00235_log : RationalLog.accepts (944816953/2147483648) (-440803695/1073741824) 2 8=true := by decide +kernel
#print axioms leaf00235_log
def leaf00235 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (146536940529/500000000000) (944816953/2147483648) (-440803695/1073741824) 2 8 ![52,0,4] ![(139/3200),0,(1/4)] ![(3/3200),1,(1/4)] affine00235
theorem leaf00235_checked : FastNestedCellData.accepts 1 0 4 leaf00235=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (146536940529/500000000000) (944816953/2147483648) (-440803695/1073741824) 2 8 ![52,0,4] ![(139/3200),0,(1/4)] ![(3/3200),1,(1/4)] 337891179910357469696630980608000000000000 192228601565268057671244452535112254357504 655904923602610537997048741888000000000000 raw00235 affine00235
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00235_raw leaf00235_rectangular
    leaf00235_transform leaf00235_sign leaf00235_log
#print axioms leaf00235_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
