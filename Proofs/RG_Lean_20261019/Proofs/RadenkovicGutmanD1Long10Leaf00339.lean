/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00339 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 1876717200765562548282982400000000000 735463747098545118439876740715118592 1103067851680839489080524800000000000))
theorem leaf00339_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 1876717200765562548282982400000000000 735463747098545118439876740715118592 1103067851680839489080524800000000000 raw00339=true := by decide +kernel
#print axioms leaf00339_raw
theorem leaf00339_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00339=true := by decide +kernel
#print axioms leaf00339_rectangular
def affine00339 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00339 (IntegerComputedClassCell.leftNumerator ![(11/80),0,0] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/80),0,0] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/80),0,0] ![(1/160),1,(1/4)]))
theorem leaf00339_transform : affine00339=(NestedInteger.clearedAll 3 raw00339 (IntegerComputedClassCell.leftNumerator ![(11/80),0,0] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/80),0,0] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/80),0,0] ![(1/160),1,(1/4)])) := by decide +kernel
#print axioms leaf00339_transform
theorem leaf00339_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00339=true := by decide +kernel
#print axioms leaf00339_sign
theorem leaf00339_log : RationalLog.accepts (126230249/536870912) (-3108804951/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00339_log
def leaf00339 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (2083574647/3125000000) (126230249/536870912) (-3108804951/4294967296) 3 8 ![52,0,4] ![(11/80),0,0] ![(1/160),1,(1/4)] affine00339
theorem leaf00339_checked : FastNestedCellData.accepts 1 0 4 leaf00339=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (2083574647/3125000000) (126230249/536870912) (-3108804951/4294967296) 3 8 ![52,0,4] ![(11/80),0,0] ![(1/160),1,(1/4)] 1876717200765562548282982400000000000 735463747098545118439876740715118592 1103067851680839489080524800000000000 raw00339 affine00339
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00339_raw leaf00339_rectangular
    leaf00339_transform leaf00339_sign leaf00339_log
#print axioms leaf00339_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
