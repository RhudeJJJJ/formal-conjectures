/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00506 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 17878788959592463060878617477120000000000 7688728157816143362966520091054048280576 19832439560099780015991816192000000000000))
theorem leaf00506_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 17878788959592463060878617477120000000000 7688728157816143362966520091054048280576 19832439560099780015991816192000000000000 raw00506=true := by decide +kernel
#print axioms leaf00506_raw
theorem leaf00506_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00506=true := by decide +kernel
#print axioms leaf00506_rectangular
def affine00506 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00506 (IntegerComputedClassCell.leftNumerator ![(11/800),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/800),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/800),0,(1/16)] ![(1/3200),1,(1/16)]))
theorem leaf00506_transform : affine00506=(NestedInteger.clearedAll 3 raw00506 (IntegerComputedClassCell.leftNumerator ![(11/800),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/800),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/800),0,(1/16)] ![(1/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00506_transform
theorem leaf00506_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00506=true := by decide +kernel
#print axioms leaf00506_sign
theorem leaf00506_log : RationalLog.accepts (1331022975/4294967296) (-628942219/1073741824) 2 8=true := by decide +kernel
#print axioms leaf00506_log
def leaf00506 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (96921109157/250000000000) (1331022975/4294967296) (-628942219/1073741824) 2 8 ![60,0,4] ![(11/800),0,(1/16)] ![(1/3200),1,(1/16)] affine00506
theorem leaf00506_checked : FastNestedCellData.accepts 1 2 4 leaf00506=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (96921109157/250000000000) (1331022975/4294967296) (-628942219/1073741824) 2 8 ![60,0,4] ![(11/800),0,(1/16)] ![(1/3200),1,(1/16)] 17878788959592463060878617477120000000000 7688728157816143362966520091054048280576 19832439560099780015991816192000000000000 raw00506 affine00506
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00506_raw leaf00506_rectangular
    leaf00506_transform leaf00506_sign leaf00506_log
#print axioms leaf00506_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
