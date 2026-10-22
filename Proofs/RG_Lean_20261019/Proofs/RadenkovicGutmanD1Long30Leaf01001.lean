/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01001 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 5706419889997700393001790996480000000000 3201945463940735652064328849681603887104 5175352467036363560057202278400000000000))
theorem leaf01001_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 5706419889997700393001790996480000000000 3201945463940735652064328849681603887104 5175352467036363560057202278400000000000 raw01001=true := by decide +kernel
#print axioms leaf01001_raw
theorem leaf01001_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01001=true := by decide +kernel
#print axioms leaf01001_rectangular
def affine01001 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01001 (IntegerComputedClassCell.leftNumerator ![(3/20),0,(1/16)] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/20),0,(1/16)] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/20),0,(1/16)] ![(1/160),1,(1/16)]))
theorem leaf01001_transform : affine01001=(NestedInteger.clearedAll 3 raw01001 (IntegerComputedClassCell.leftNumerator ![(3/20),0,(1/16)] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/20),0,(1/16)] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/20),0,(1/16)] ![(1/160),1,(1/16)])) := by decide +kernel
#print axioms leaf01001_transform
theorem leaf01001_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01001=true := by decide +kernel
#print axioms leaf01001_sign
theorem leaf01001_log : RationalLog.accepts (372208295/1073741824) (-568788565/1073741824) 2 8=true := by decide +kernel
#print axioms leaf01001_log
def leaf01001 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (123738256837/200000000000) (372208295/1073741824) (-568788565/1073741824) 2 8 ![60,0,4] ![(3/20),0,(1/16)] ![(1/160),1,(1/16)] affine01001
theorem leaf01001_checked : FastNestedCellData.accepts 1 2 4 leaf01001=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (123738256837/200000000000) (372208295/1073741824) (-568788565/1073741824) 2 8 ![60,0,4] ![(3/20),0,(1/16)] ![(1/160),1,(1/16)] 5706419889997700393001790996480000000000 3201945463940735652064328849681603887104 5175352467036363560057202278400000000000 raw01001 affine01001
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01001_raw leaf01001_rectangular
    leaf01001_transform leaf01001_sign leaf01001_log
#print axioms leaf01001_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
