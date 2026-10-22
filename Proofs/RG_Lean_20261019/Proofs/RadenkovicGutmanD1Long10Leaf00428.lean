/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00428 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 95186523924235894794930356224000000000000 113190520157187428156510680668298153033728 5483960519904183554048878706688000000000000))
theorem leaf00428_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 95186523924235894794930356224000000000000 113190520157187428156510680668298153033728 5483960519904183554048878706688000000000000 raw00428=true := by decide +kernel
#print axioms leaf00428_raw
theorem leaf00428_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00428=true := by decide +kernel
#print axioms leaf00428_rectangular
def affine00428 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00428 (IntegerComputedClassCell.leftNumerator ![(3/8),0,(3/4)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/8),0,(3/4)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/8),0,(3/4)] ![(1/32),1,(1/4)]))
theorem leaf00428_transform : affine00428=(NestedInteger.clearedAll 3 raw00428 (IntegerComputedClassCell.leftNumerator ![(3/8),0,(3/4)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/8),0,(3/4)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/8),0,(3/4)] ![(1/32),1,(1/4)])) := by decide +kernel
#print axioms leaf00428_transform
theorem leaf00428_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00428=true := by decide +kernel
#print axioms leaf00428_sign
theorem leaf00428_log : RationalLog.accepts (5004051177/4294967296) (328143831/4294967296) 0 8=true := by decide +kernel
#print axioms leaf00428_log
def leaf00428 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (10320143603/500000000000) (5004051177/4294967296) (328143831/4294967296) 0 8 ![52,0,4] ![(3/8),0,(3/4)] ![(1/32),1,(1/4)] affine00428
theorem leaf00428_checked : FastNestedCellData.accepts 1 0 4 leaf00428=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (10320143603/500000000000) (5004051177/4294967296) (328143831/4294967296) 0 8 ![52,0,4] ![(3/8),0,(3/4)] ![(1/32),1,(1/4)] 95186523924235894794930356224000000000000 113190520157187428156510680668298153033728 5483960519904183554048878706688000000000000 raw00428 affine00428
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00428_raw leaf00428_rectangular
    leaf00428_transform leaf00428_sign leaf00428_log
#print axioms leaf00428_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
