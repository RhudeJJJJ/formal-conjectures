/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00180 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 16032354550306343398698437836800000000000 5029408804264652603935984147715063808 14467029275584301359326822400000000000))
theorem leaf00180_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 16032354550306343398698437836800000000000 5029408804264652603935984147715063808 14467029275584301359326822400000000000 raw00180=true := by decide +kernel
#print axioms leaf00180_raw
theorem leaf00180_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00180=true := by decide +kernel
#print axioms leaf00180_rectangular
def affine00180 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00180 (IntegerComputedClassCell.leftNumerator ![(31/8000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(31/8000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(31/8000),0,0] ![(3/32000),1,(1/16)]))
theorem leaf00180_transform : affine00180=(NestedInteger.clearedAll 3 raw00180 (IntegerComputedClassCell.leftNumerator ![(31/8000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(31/8000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(31/8000),0,0] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00180_transform
theorem leaf00180_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00180=true := by decide +kernel
#print axioms leaf00180_sign
theorem leaf00180_log : RationalLog.accepts (499889/2147483648) (-17964605791/4294967296) 13 8=true := by decide +kernel
#print axioms leaf00180_log
def leaf00180 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (34764627267/100000000000) (499889/2147483648) (-17964605791/4294967296) 13 8 ![60,0,4] ![(31/8000),0,0] ![(3/32000),1,(1/16)] affine00180
theorem leaf00180_checked : FastNestedCellData.accepts 1 2 4 leaf00180=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (34764627267/100000000000) (499889/2147483648) (-17964605791/4294967296) 13 8 ![60,0,4] ![(31/8000),0,0] ![(3/32000),1,(1/16)] 16032354550306343398698437836800000000000 5029408804264652603935984147715063808 14467029275584301359326822400000000000 raw00180 affine00180
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00180_raw leaf00180_rectangular
    leaf00180_transform leaf00180_sign leaf00180_log
#print axioms leaf00180_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
