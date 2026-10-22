/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01198 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 122319534749201114414972928000000000000 143047436168709667792091657240058003456 7660750705664379094986391552000000000000))
theorem leaf01198_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 122319534749201114414972928000000000000 143047436168709667792091657240058003456 7660750705664379094986391552000000000000 raw01198=true := by decide +kernel
#print axioms leaf01198_raw
theorem leaf01198_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01198=true := by decide +kernel
#print axioms leaf01198_rectangular
def affine01198 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01198 (IntegerComputedClassCell.leftNumerator ![(3/8),0,(7/8)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/8),0,(7/8)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/8),0,(7/8)] ![(1/32),1,(1/16)]))
theorem leaf01198_transform : affine01198=(NestedInteger.clearedAll 3 raw01198 (IntegerComputedClassCell.leftNumerator ![(3/8),0,(7/8)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/8),0,(7/8)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/8),0,(7/8)] ![(1/32),1,(1/16)])) := by decide +kernel
#print axioms leaf01198_transform
theorem leaf01198_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01198=true := by decide +kernel
#print axioms leaf01198_sign
theorem leaf01198_log : RationalLog.accepts (1232677391/1073741824) (296436419/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01198_log
def leaf01198 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (4668192507/250000000000) (1232677391/1073741824) (296436419/4294967296) 0 8 ![60,0,4] ![(3/8),0,(7/8)] ![(1/32),1,(1/16)] affine01198
theorem leaf01198_checked : FastNestedCellData.accepts 1 2 4 leaf01198=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (4668192507/250000000000) (1232677391/1073741824) (296436419/4294967296) 0 8 ![60,0,4] ![(3/8),0,(7/8)] ![(1/32),1,(1/16)] 122319534749201114414972928000000000000 143047436168709667792091657240058003456 7660750705664379094986391552000000000000 raw01198 affine01198
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01198_raw leaf01198_rectangular
    leaf01198_transform leaf01198_sign leaf01198_log
#print axioms leaf01198_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
