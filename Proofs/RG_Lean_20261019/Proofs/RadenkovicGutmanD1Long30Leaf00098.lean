/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00098 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 81766123841801512571774173184000000000000 78382648387243940855474720328747369627648 4420854831692101180142269759488000000000000))
theorem leaf00098_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 81766123841801512571774173184000000000000 78382648387243940855474720328747369627648 4420854831692101180142269759488000000000000 raw00098=true := by decide +kernel
#print axioms leaf00098_raw
theorem leaf00098_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00098=true := by decide +kernel
#print axioms leaf00098_rectangular
def affine00098 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00098 (IntegerComputedClassCell.leftNumerator ![(73/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(73/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(73/32000),0,(1/4)] ![(3/32000),1,(1/4)]))
theorem leaf00098_transform : affine00098=(NestedInteger.clearedAll 3 raw00098 (IntegerComputedClassCell.leftNumerator ![(73/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(73/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(73/32000),0,(1/4)] ![(3/32000),1,(1/4)])) := by decide +kernel
#print axioms leaf00098_transform
theorem leaf00098_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00098=true := by decide +kernel
#print axioms leaf00098_sign
theorem leaf00098_log : RationalLog.accepts (2022757061/2147483648) (-501935/16777216) 1 8=true := by decide +kernel
#print axioms leaf00098_log
def leaf00098 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (17730201821/1000000000000) (2022757061/2147483648) (-501935/16777216) 1 8 ![60,0,4] ![(73/32000),0,(1/4)] ![(3/32000),1,(1/4)] affine00098
theorem leaf00098_checked : FastNestedCellData.accepts 1 2 4 leaf00098=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (17730201821/1000000000000) (2022757061/2147483648) (-501935/16777216) 1 8 ![60,0,4] ![(73/32000),0,(1/4)] ![(3/32000),1,(1/4)] 81766123841801512571774173184000000000000 78382648387243940855474720328747369627648 4420854831692101180142269759488000000000000 raw00098 affine00098
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00098_raw leaf00098_rectangular
    leaf00098_transform leaf00098_sign leaf00098_log
#print axioms leaf00098_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
