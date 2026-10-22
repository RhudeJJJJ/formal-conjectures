/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01078 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 469474424316194863093662089216000000000000 486138373259438923453189292253404624584704 1591792454755490179304958984192000000000000))
theorem leaf01078_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 469474424316194863093662089216000000000000 486138373259438923453189292253404624584704 1591792454755490179304958984192000000000000 raw01078=true := by decide +kernel
#print axioms leaf01078_raw
theorem leaf01078_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01078=true := by decide +kernel
#print axioms leaf01078_rectangular
def affine01078 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01078 (IntegerComputedClassCell.leftNumerator ![(59/160),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(59/160),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(59/160),0,(1/4)] ![(3/160),1,(1/4)]))
theorem leaf01078_transform : affine01078=(NestedInteger.clearedAll 3 raw01078 (IntegerComputedClassCell.leftNumerator ![(59/160),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(59/160),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(59/160),0,(1/4)] ![(3/160),1,(1/4)])) := by decide +kernel
#print axioms leaf01078_transform
theorem leaf01078_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01078=true := by decide +kernel
#print axioms leaf01078_sign
theorem leaf01078_log : RationalLog.accepts (3406929777/4294967296) (-497426857/4294967296) 1 8=true := by decide +kernel
#print axioms leaf01078_log
def leaf01078 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (152701557231/500000000000) (3406929777/4294967296) (-497426857/4294967296) 1 8 ![60,0,4] ![(59/160),0,(1/4)] ![(3/160),1,(1/4)] affine01078
theorem leaf01078_checked : FastNestedCellData.accepts 1 2 4 leaf01078=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (152701557231/500000000000) (3406929777/4294967296) (-497426857/4294967296) 1 8 ![60,0,4] ![(59/160),0,(1/4)] ![(3/160),1,(1/4)] 469474424316194863093662089216000000000000 486138373259438923453189292253404624584704 1591792454755490179304958984192000000000000 raw01078 affine01078
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01078_raw leaf01078_rectangular
    leaf01078_transform leaf01078_sign leaf01078_log
#print axioms leaf01078_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
