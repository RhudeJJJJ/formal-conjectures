/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00195 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 31560365841807502341828090265600000000000 690636052708328980694853821946296008704 1261470099895740179826081792000000000000))
theorem leaf00195_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 31560365841807502341828090265600000000000 690636052708328980694853821946296008704 1261470099895740179826081792000000000000 raw00195=true := by decide +kernel
#print axioms leaf00195_raw
theorem leaf00195_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00195=true := by decide +kernel
#print axioms leaf00195_rectangular
def affine00195 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00195 (IntegerComputedClassCell.leftNumerator ![(1/32),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/32),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/32),0,0] ![(3/3200),1,(1/4)]))
theorem leaf00195_transform : affine00195=(NestedInteger.clearedAll 3 raw00195 (IntegerComputedClassCell.leftNumerator ![(1/32),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/32),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/32),0,0] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00195_transform
theorem leaf00195_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00195=true := by decide +kernel
#print axioms leaf00195_sign
theorem leaf00195_log : RationalLog.accepts (15183805/1073741824) (-9145436159/4294967296) 7 8=true := by decide +kernel
#print axioms leaf00195_log
def leaf00195 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (273742537681/500000000000) (15183805/1073741824) (-9145436159/4294967296) 7 8 ![52,0,4] ![(1/32),0,0] ![(3/3200),1,(1/4)] affine00195
theorem leaf00195_checked : FastNestedCellData.accepts 1 0 4 leaf00195=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (273742537681/500000000000) (15183805/1073741824) (-9145436159/4294967296) 7 8 ![52,0,4] ![(1/32),0,0] ![(3/3200),1,(1/4)] 31560365841807502341828090265600000000000 690636052708328980694853821946296008704 1261470099895740179826081792000000000000 raw00195 affine00195
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00195_raw leaf00195_rectangular
    leaf00195_transform leaf00195_sign leaf00195_log
#print axioms leaf00195_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
