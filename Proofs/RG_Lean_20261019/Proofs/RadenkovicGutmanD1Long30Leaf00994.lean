/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00994 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 504058252767711189646304083968000000000000 347133114857013888050048129617172203831296 1058653388789291066255837495296000000000000))
theorem leaf00994_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 504058252767711189646304083968000000000000 347133114857013888050048129617172203831296 1058653388789291066255837495296000000000000 raw00994=true := by decide +kernel
#print axioms leaf00994_raw
theorem leaf00994_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00994=true := by decide +kernel
#print axioms leaf00994_rectangular
def affine00994 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00994 (IntegerComputedClassCell.leftNumerator ![(11/80),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/80),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/80),0,(1/2)] ![(1/160),1,(1/2)]))
theorem leaf00994_transform : affine00994=(NestedInteger.clearedAll 3 raw00994 (IntegerComputedClassCell.leftNumerator ![(11/80),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/80),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/80),0,(1/2)] ![(1/160),1,(1/2)])) := by decide +kernel
#print axioms leaf00994_transform
theorem leaf00994_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00994=true := by decide +kernel
#print axioms leaf00994_sign
theorem leaf00994_log : RationalLog.accepts (2227458387/4294967296) (-705000369/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00994_log
def leaf00994 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (163950315813/500000000000) (2227458387/4294967296) (-705000369/2147483648) 1 8 ![60,0,4] ![(11/80),0,(1/2)] ![(1/160),1,(1/2)] affine00994
theorem leaf00994_checked : FastNestedCellData.accepts 1 2 4 leaf00994=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (163950315813/500000000000) (2227458387/4294967296) (-705000369/2147483648) 1 8 ![60,0,4] ![(11/80),0,(1/2)] ![(1/160),1,(1/2)] 504058252767711189646304083968000000000000 347133114857013888050048129617172203831296 1058653388789291066255837495296000000000000 raw00994 affine00994
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00994_raw leaf00994_rectangular
    leaf00994_transform leaf00994_sign leaf00994_log
#print axioms leaf00994_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
