/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00789 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 10844222361265553672256251494400000000000 8136728603147797140999557218443385110528 57671320703927569199040299008000000000000))
theorem leaf00789_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 10844222361265553672256251494400000000000 8136728603147797140999557218443385110528 57671320703927569199040299008000000000000 raw00789=true := by decide +kernel
#print axioms leaf00789_raw
theorem leaf00789_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00789=true := by decide +kernel
#print axioms leaf00789_rectangular
def affine00789 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00789 (IntegerComputedClassCell.leftNumerator ![(127/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(127/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(127/3200),0,(1/2)] ![(3/3200),1,(1/2)]))
theorem leaf00789_transform : affine00789=(NestedInteger.clearedAll 3 raw00789 (IntegerComputedClassCell.leftNumerator ![(127/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(127/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(127/3200),0,(1/2)] ![(3/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00789_transform
theorem leaf00789_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00789=true := by decide +kernel
#print axioms leaf00789_sign
theorem leaf00789_log : RationalLog.accepts (2824178595/4294967296) (-900281835/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00789_log
def leaf00789 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (35271988329/250000000000) (2824178595/4294967296) (-900281835/4294967296) 1 8 ![60,0,4] ![(127/3200),0,(1/2)] ![(3/3200),1,(1/2)] affine00789
theorem leaf00789_checked : FastNestedCellData.accepts 1 2 4 leaf00789=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (35271988329/250000000000) (2824178595/4294967296) (-900281835/4294967296) 1 8 ![60,0,4] ![(127/3200),0,(1/2)] ![(3/3200),1,(1/2)] 10844222361265553672256251494400000000000 8136728603147797140999557218443385110528 57671320703927569199040299008000000000000 raw00789 affine00789
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00789_raw leaf00789_rectangular
    leaf00789_transform leaf00789_sign leaf00789_log
#print axioms leaf00789_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
