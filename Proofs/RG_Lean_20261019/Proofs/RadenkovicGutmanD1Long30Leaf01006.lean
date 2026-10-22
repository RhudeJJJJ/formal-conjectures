/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01006 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 684324617782552840860860416000000000000 398838551536492000385383194048528908288 656197769817586447450898432000000000000))
theorem leaf01006_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 684324617782552840860860416000000000000 398838551536492000385383194048528908288 656197769817586447450898432000000000000 raw01006=true := by decide +kernel
#print axioms leaf01006_raw
theorem leaf01006_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01006=true := by decide +kernel
#print axioms leaf01006_rectangular
def affine01006 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01006 (IntegerComputedClassCell.leftNumerator ![(5/32),0,(1/16)] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(5/32),0,(1/16)] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(5/32),0,(1/16)] ![(1/160),1,(1/16)]))
theorem leaf01006_transform : affine01006=(NestedInteger.clearedAll 3 raw01006 (IntegerComputedClassCell.leftNumerator ![(5/32),0,(1/16)] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(5/32),0,(1/16)] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(5/32),0,(1/16)] ![(1/160),1,(1/16)])) := by decide +kernel
#print axioms leaf01006_transform
theorem leaf01006_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01006=true := by decide +kernel
#print axioms leaf01006_sign
theorem leaf01006_log : RationalLog.accepts (194613149/536870912) (-544786523/1073741824) 2 8=true := by decide +kernel
#print axioms leaf01006_log
def leaf01006 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (37987647349/62500000000) (194613149/536870912) (-544786523/1073741824) 2 8 ![60,0,4] ![(5/32),0,(1/16)] ![(1/160),1,(1/16)] affine01006
theorem leaf01006_checked : FastNestedCellData.accepts 1 2 4 leaf01006=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (37987647349/62500000000) (194613149/536870912) (-544786523/1073741824) 2 8 ![60,0,4] ![(5/32),0,(1/16)] ![(1/160),1,(1/16)] 684324617782552840860860416000000000000 398838551536492000385383194048528908288 656197769817586447450898432000000000000 raw01006 affine01006
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01006_raw leaf01006_rectangular
    leaf01006_transform leaf01006_sign leaf01006_log
#print axioms leaf01006_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
