/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01049 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 6092131224232820738233785647104000000000000 5293467502304244175752241728593657650479104 16028420380882650837415274479616000000000000))
theorem leaf01049_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 6092131224232820738233785647104000000000000 5293467502304244175752241728593657650479104 16028420380882650837415274479616000000000000 raw01049=true := by decide +kernel
#print axioms leaf01049_raw
theorem leaf01049_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01049=true := by decide +kernel
#print axioms leaf01049_rectangular
def affine01049 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01049 (IntegerComputedClassCell.leftNumerator ![(41/160),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(41/160),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(41/160),0,(1/2)] ![(3/160),1,(1/2)]))
theorem leaf01049_transform : affine01049=(NestedInteger.clearedAll 3 raw01049 (IntegerComputedClassCell.leftNumerator ![(41/160),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(41/160),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(41/160),0,(1/2)] ![(3/160),1,(1/2)])) := by decide +kernel
#print axioms leaf01049_transform
theorem leaf01049_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01049=true := by decide +kernel
#print axioms leaf01049_sign
theorem leaf01049_log : RationalLog.accepts (2805407359/4294967296) (-914602985/4294967296) 1 8=true := by decide +kernel
#print axioms leaf01049_log
def leaf01049 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (330255095419/1000000000000) (2805407359/4294967296) (-914602985/4294967296) 1 8 ![60,0,4] ![(41/160),0,(1/2)] ![(3/160),1,(1/2)] affine01049
theorem leaf01049_checked : FastNestedCellData.accepts 1 2 4 leaf01049=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (330255095419/1000000000000) (2805407359/4294967296) (-914602985/4294967296) 1 8 ![60,0,4] ![(41/160),0,(1/2)] ![(3/160),1,(1/2)] 6092131224232820738233785647104000000000000 5293467502304244175752241728593657650479104 16028420380882650837415274479616000000000000 raw01049 affine01049
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01049_raw leaf01049_rectangular
    leaf01049_transform leaf01049_sign leaf01049_log
#print axioms leaf01049_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
