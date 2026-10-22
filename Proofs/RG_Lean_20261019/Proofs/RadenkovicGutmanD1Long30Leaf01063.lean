/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01063 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 6353883311326885516684650610688000000000000 6099132090123044822328620015869950443913216 17707144312468287148586132570112000000000000))
theorem leaf01063_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 6353883311326885516684650610688000000000000 6099132090123044822328620015869950443913216 17707144312468287148586132570112000000000000 raw01063=true := by decide +kernel
#print axioms leaf01063_raw
theorem leaf01063_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01063=true := by decide +kernel
#print axioms leaf01063_rectangular
def affine01063 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01063 (IntegerComputedClassCell.leftNumerator ![(5/16),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(5/16),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(5/16),0,(1/4)] ![(3/160),1,(1/4)]))
theorem leaf01063_transform : affine01063=(NestedInteger.clearedAll 3 raw01063 (IntegerComputedClassCell.leftNumerator ![(5/16),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(5/16),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(5/16),0,(1/4)] ![(3/160),1,(1/4)])) := by decide +kernel
#print axioms leaf01063_transform
theorem leaf01063_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01063=true := by decide +kernel
#print axioms leaf01063_sign
theorem leaf01063_log : RationalLog.accepts (3066519429/4294967296) (-723488907/4294967296) 1 8=true := by decide +kernel
#print axioms leaf01063_log
def leaf01063 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (344444704493/1000000000000) (3066519429/4294967296) (-723488907/4294967296) 1 8 ![60,0,4] ![(5/16),0,(1/4)] ![(3/160),1,(1/4)] affine01063
theorem leaf01063_checked : FastNestedCellData.accepts 1 2 4 leaf01063=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (344444704493/1000000000000) (3066519429/4294967296) (-723488907/4294967296) 1 8 ![60,0,4] ![(5/16),0,(1/4)] ![(3/160),1,(1/4)] 6353883311326885516684650610688000000000000 6099132090123044822328620015869950443913216 17707144312468287148586132570112000000000000 raw01063 affine01063
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01063_raw leaf01063_rectangular
    leaf01063_transform leaf01063_sign leaf01063_log
#print axioms leaf01063_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
