/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00247 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 89861806348543447273100541952000000000000 49927433205432450056989051754105695895552 160141482102807883296165330944000000000000))
theorem leaf00247_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 89861806348543447273100541952000000000000 49927433205432450056989051754105695895552 160141482102807883296165330944000000000000 raw00247=true := by decide +kernel
#print axioms leaf00247_raw
theorem leaf00247_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00247=true := by decide +kernel
#print axioms leaf00247_rectangular
def affine00247 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00247 (IntegerComputedClassCell.leftNumerator ![(151/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(151/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(151/3200),0,(1/4)] ![(3/3200),1,(1/4)]))
theorem leaf00247_transform : affine00247=(NestedInteger.clearedAll 3 raw00247 (IntegerComputedClassCell.leftNumerator ![(151/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(151/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(151/3200),0,(1/4)] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00247_transform
theorem leaf00247_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00247=true := by decide +kernel
#print axioms leaf00247_sign
theorem leaf00247_log : RationalLog.accepts (227392439/536870912) (-1844861069/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00247_log
def leaf00247 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (311770770133/1000000000000) (227392439/536870912) (-1844861069/4294967296) 2 8 ![52,0,4] ![(151/3200),0,(1/4)] ![(3/3200),1,(1/4)] affine00247
theorem leaf00247_checked : FastNestedCellData.accepts 1 0 4 leaf00247=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (311770770133/1000000000000) (227392439/536870912) (-1844861069/4294967296) 2 8 ![52,0,4] ![(151/3200),0,(1/4)] ![(3/3200),1,(1/4)] 89861806348543447273100541952000000000000 49927433205432450056989051754105695895552 160141482102807883296165330944000000000000 raw00247 affine00247
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00247_raw leaf00247_rectangular
    leaf00247_transform leaf00247_sign leaf00247_log
#print axioms leaf00247_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
