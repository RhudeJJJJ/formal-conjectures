/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00250 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 20790432281486107318374576947200000000000 14763023125750317031205593366472425472 32746999397107473119077990400000000000))
theorem leaf00250_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 20790432281486107318374576947200000000000 14763023125750317031205593366472425472 32746999397107473119077990400000000000 raw00250=true := by decide +kernel
#print axioms leaf00250_raw
theorem leaf00250_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00250=true := by decide +kernel
#print axioms leaf00250_rectangular
def affine00250 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00250 (IntegerComputedClassCell.leftNumerator ![(17/3200),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/3200),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/3200),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00250_transform : affine00250=(NestedInteger.clearedAll 3 raw00250 (IntegerComputedClassCell.leftNumerator ![(17/3200),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/3200),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/3200),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00250_transform
theorem leaf00250_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00250=true := by decide +kernel
#print axioms leaf00250_sign
theorem leaf00250_log : RationalLog.accepts (1051061/2147483648) (-4092165431/1073741824) 11 8=true := by decide +kernel
#print axioms leaf00250_log
def leaf00250 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (45082063693/100000000000) (1051061/2147483648) (-4092165431/1073741824) 11 8 ![60,0,4] ![(17/3200),0,0] ![(1/6400),1,(1/16)] affine00250
theorem leaf00250_checked : FastNestedCellData.accepts 1 2 4 leaf00250=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (45082063693/100000000000) (1051061/2147483648) (-4092165431/1073741824) 11 8 ![60,0,4] ![(17/3200),0,0] ![(1/6400),1,(1/16)] 20790432281486107318374576947200000000000 14763023125750317031205593366472425472 32746999397107473119077990400000000000 raw00250 affine00250
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00250_raw leaf00250_rectangular
    leaf00250_transform leaf00250_sign leaf00250_log
#print axioms leaf00250_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
