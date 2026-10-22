/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00551 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 328181126193747016470076221030400000000000 125581971872148233356195769877694938873856 282353652967804197518012160409600000000000))
theorem leaf00551_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 328181126193747016470076221030400000000000 125581971872148233356195769877694938873856 282353652967804197518012160409600000000000 raw00551=true := by decide +kernel
#print axioms leaf00551_raw
theorem leaf00551_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00551=true := by decide +kernel
#print axioms leaf00551_rectangular
def affine00551 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00551 (IntegerComputedClassCell.leftNumerator ![(53/3200),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(53/3200),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(53/3200),0,(1/16)] ![(1/3200),1,(1/16)]))
theorem leaf00551_transform : affine00551=(NestedInteger.clearedAll 3 raw00551 (IntegerComputedClassCell.leftNumerator ![(53/3200),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(53/3200),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(53/3200),0,(1/16)] ![(1/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00551_transform
theorem leaf00551_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00551=true := by decide +kernel
#print axioms leaf00551_sign
theorem leaf00551_log : RationalLog.accepts (1137562679/4294967296) (-22289471/33554432) 2 8=true := by decide +kernel
#print axioms leaf00551_log
def leaf00551 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (88953672497/200000000000) (1137562679/4294967296) (-22289471/33554432) 2 8 ![60,0,4] ![(53/3200),0,(1/16)] ![(1/3200),1,(1/16)] affine00551
theorem leaf00551_checked : FastNestedCellData.accepts 1 2 4 leaf00551=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (88953672497/200000000000) (1137562679/4294967296) (-22289471/33554432) 2 8 ![60,0,4] ![(53/3200),0,(1/16)] ![(1/3200),1,(1/16)] 328181126193747016470076221030400000000000 125581971872148233356195769877694938873856 282353652967804197518012160409600000000000 raw00551 affine00551
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00551_raw leaf00551_rectangular
    leaf00551_transform leaf00551_sign leaf00551_log
#print axioms leaf00551_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
