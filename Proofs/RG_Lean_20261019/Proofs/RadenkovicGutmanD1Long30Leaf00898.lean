/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00898 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 354346596406710718403811318169600000000000 187125609990865804183405475835791007547392 487073711465303120099583983616000000000000))
theorem leaf00898_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 354346596406710718403811318169600000000000 187125609990865804183405475835791007547392 487073711465303120099583983616000000000000 raw00898=true := by decide +kernel
#print axioms leaf00898_raw
theorem leaf00898_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00898=true := by decide +kernel
#print axioms leaf00898_rectangular
def affine00898 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00898 (IntegerComputedClassCell.leftNumerator ![(43/640),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(43/640),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(43/640),0,(1/4)] ![(1/640),1,(1/4)]))
theorem leaf00898_transform : affine00898=(NestedInteger.clearedAll 3 raw00898 (IntegerComputedClassCell.leftNumerator ![(43/640),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(43/640),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(43/640),0,(1/4)] ![(1/640),1,(1/4)])) := by decide +kernel
#print axioms leaf00898_transform
theorem leaf00898_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00898=true := by decide +kernel
#print axioms leaf00898_sign
theorem leaf00898_log : RationalLog.accepts (819296705/2147483648) (-2069327649/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00898_log
def leaf00898 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (384183349637/1000000000000) (819296705/2147483648) (-2069327649/4294967296) 2 8 ![60,0,4] ![(43/640),0,(1/4)] ![(1/640),1,(1/4)] affine00898
theorem leaf00898_checked : FastNestedCellData.accepts 1 2 4 leaf00898=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (384183349637/1000000000000) (819296705/2147483648) (-2069327649/4294967296) 2 8 ![60,0,4] ![(43/640),0,(1/4)] ![(1/640),1,(1/4)] 354346596406710718403811318169600000000000 187125609990865804183405475835791007547392 487073711465303120099583983616000000000000 raw00898 affine00898
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00898_raw leaf00898_rectangular
    leaf00898_transform leaf00898_sign leaf00898_log
#print axioms leaf00898_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
