/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00042 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 109873280180678364563668729856000000000000 103860928445543965486592524535937858797568 4359330956403282916100341235712000000000000))
theorem leaf00042_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 109873280180678364563668729856000000000000 103860928445543965486592524535937858797568 4359330956403282916100341235712000000000000 raw00042=true := by decide +kernel
#print axioms leaf00042_raw
theorem leaf00042_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00042=true := by decide +kernel
#print axioms leaf00042_rectangular
def affine00042 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00042 (IntegerComputedClassCell.leftNumerator ![(3/2000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(3/2000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(3/2000),0,(1/8)] ![(1/16000),1,(1/8)]))
theorem leaf00042_transform : affine00042=(NestedInteger.clearedAll 3 raw00042 (IntegerComputedClassCell.leftNumerator ![(3/2000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(3/2000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(3/2000),0,(1/8)] ![(1/16000),1,(1/8)])) := by decide +kernel
#print axioms leaf00042_transform
theorem leaf00042_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00042=true := by decide +kernel
#print axioms leaf00042_sign
theorem leaf00042_log : RationalLog.accepts (3965466217/4294967296) (-171413275/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00042_log
def leaf00042 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (11912484907/500000000000) (3965466217/4294967296) (-171413275/4294967296) 1 8 ![60,0,4] ![(3/2000),0,(1/8)] ![(1/16000),1,(1/8)] affine00042
theorem leaf00042_checked : FastNestedCellData.accepts 1 2 4 leaf00042=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (11912484907/500000000000) (3965466217/4294967296) (-171413275/4294967296) 1 8 ![60,0,4] ![(3/2000),0,(1/8)] ![(1/16000),1,(1/8)] 109873280180678364563668729856000000000000 103860928445543965486592524535937858797568 4359330956403282916100341235712000000000000 raw00042 affine00042
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00042_raw leaf00042_rectangular
    leaf00042_transform leaf00042_sign leaf00042_log
#print axioms leaf00042_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
