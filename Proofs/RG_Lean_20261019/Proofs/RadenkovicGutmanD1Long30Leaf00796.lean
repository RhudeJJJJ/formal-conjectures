/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00796 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 21605064257504492874891264000000000000 5413991603040416434973153598281613312 7837170552106203240988672000000000000))
theorem leaf00796_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 21605064257504492874891264000000000000 5413991603040416434973153598281613312 7837170552106203240988672000000000000 raw00796=true := by decide +kernel
#print axioms leaf00796_raw
theorem leaf00796_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00796=true := by decide +kernel
#print axioms leaf00796_rectangular
def affine00796 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00796 (IntegerComputedClassCell.leftNumerator ![(133/3200),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(133/3200),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(133/3200),0,(1/16)] ![(3/3200),1,(1/16)]))
theorem leaf00796_transform : affine00796=(NestedInteger.clearedAll 3 raw00796 (IntegerComputedClassCell.leftNumerator ![(133/3200),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(133/3200),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(133/3200),0,(1/16)] ![(3/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00796_transform
theorem leaf00796_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00796=true := by decide +kernel
#print axioms leaf00796_sign
theorem leaf00796_log : RationalLog.accepts (2486493/16777216) (-4099865273/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00796_log
def leaf00796 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (690809465871/1000000000000) (2486493/16777216) (-4099865273/4294967296) 3 8 ![60,0,4] ![(133/3200),0,(1/16)] ![(3/3200),1,(1/16)] affine00796
theorem leaf00796_checked : FastNestedCellData.accepts 1 2 4 leaf00796=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (690809465871/1000000000000) (2486493/16777216) (-4099865273/4294967296) 3 8 ![60,0,4] ![(133/3200),0,(1/16)] ![(3/3200),1,(1/16)] 21605064257504492874891264000000000000 5413991603040416434973153598281613312 7837170552106203240988672000000000000 raw00796 affine00796
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00796_raw leaf00796_rectangular
    leaf00796_transform leaf00796_sign leaf00796_log
#print axioms leaf00796_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
