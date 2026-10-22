/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00140 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 332229624976669982141664198656000000000000 58782947570548746112040782917021990912 203991815489126212464279552000000000000))
theorem leaf00140_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 332229624976669982141664198656000000000000 58782947570548746112040782917021990912 203991815489126212464279552000000000000 raw00140=true := by decide +kernel
#print axioms leaf00140_raw
theorem leaf00140_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00140=true := by decide +kernel
#print axioms leaf00140_rectangular
def affine00140 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00140 (IntegerComputedClassCell.leftNumerator ![(1/320),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/320),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/320),0,0] ![(3/32000),1,(1/16)]))
theorem leaf00140_transform : affine00140=(NestedInteger.clearedAll 3 raw00140 (IntegerComputedClassCell.leftNumerator ![(1/320),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/320),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/320),0,0] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00140_transform
theorem leaf00140_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00140=true := by decide +kernel
#print axioms leaf00140_sign
theorem leaf00140_log : RationalLog.accepts (147483/1073741824) (-9548729601/2147483648) 13 8=true := by decide +kernel
#print axioms leaf00140_log
def leaf00140 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (288163264931/1000000000000) (147483/1073741824) (-9548729601/2147483648) 13 8 ![60,0,4] ![(1/320),0,0] ![(3/32000),1,(1/16)] affine00140
theorem leaf00140_checked : FastNestedCellData.accepts 1 2 4 leaf00140=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (288163264931/1000000000000) (147483/1073741824) (-9548729601/2147483648) 13 8 ![60,0,4] ![(1/320),0,0] ![(3/32000),1,(1/16)] 332229624976669982141664198656000000000000 58782947570548746112040782917021990912 203991815489126212464279552000000000000 raw00140 affine00140
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00140_raw leaf00140_rectangular
    leaf00140_transform leaf00140_sign leaf00140_log
#print axioms leaf00140_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
