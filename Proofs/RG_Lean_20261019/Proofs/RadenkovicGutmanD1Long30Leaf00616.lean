/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00616 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 9354155676087103377306025984000000000000 3070608870000579704360532051743951814656 5913432891901501236530118656000000000000))
theorem leaf00616_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 9354155676087103377306025984000000000000 3070608870000579704360532051743951814656 5913432891901501236530118656000000000000 raw00616=true := by decide +kernel
#print axioms leaf00616_raw
theorem leaf00616_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00616=true := by decide +kernel
#print axioms leaf00616_rectangular
def affine00616 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00616 (IntegerComputedClassCell.leftNumerator ![(67/3200),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(67/3200),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(67/3200),0,(1/16)] ![(3/6400),1,(1/16)]))
theorem leaf00616_transform : affine00616=(NestedInteger.clearedAll 3 raw00616 (IntegerComputedClassCell.leftNumerator ![(67/3200),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(67/3200),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(67/3200),0,(1/16)] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00616_transform
theorem leaf00616_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00616=true := by decide +kernel
#print axioms leaf00616_sign
theorem leaf00616_log : RationalLog.accepts (231999841/1073741824) (-3290306203/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00616_log
def leaf00616 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (64907493797/125000000000) (231999841/1073741824) (-3290306203/4294967296) 3 8 ![60,0,4] ![(67/3200),0,(1/16)] ![(3/6400),1,(1/16)] affine00616
theorem leaf00616_checked : FastNestedCellData.accepts 1 2 4 leaf00616=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (64907493797/125000000000) (231999841/1073741824) (-3290306203/4294967296) 3 8 ![60,0,4] ![(67/3200),0,(1/16)] ![(3/6400),1,(1/16)] 9354155676087103377306025984000000000000 3070608870000579704360532051743951814656 5913432891901501236530118656000000000000 raw00616 affine00616
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00616_raw leaf00616_rectangular
    leaf00616_transform leaf00616_sign leaf00616_log
#print axioms leaf00616_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
