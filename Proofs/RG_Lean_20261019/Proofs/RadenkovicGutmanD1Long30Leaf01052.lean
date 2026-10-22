/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01052 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1860347414307516330597611995136000000000000 1672654620472679741904449590084912143138816 4146407207367310662716488679424000000000000))
theorem leaf01052_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1860347414307516330597611995136000000000000 1672654620472679741904449590084912143138816 4146407207367310662716488679424000000000000 raw01052=true := by decide +kernel
#print axioms leaf01052_raw
theorem leaf01052_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01052=true := by decide +kernel
#print axioms leaf01052_rectangular
def affine01052 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01052 (IntegerComputedClassCell.leftNumerator ![(11/40),0,(1/8)] ![(3/160),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(11/40),0,(1/8)] ![(3/160),1,(1/8)]) (IntegerComputedClassCell.denominator ![(11/40),0,(1/8)] ![(3/160),1,(1/8)]))
theorem leaf01052_transform : affine01052=(NestedInteger.clearedAll 3 raw01052 (IntegerComputedClassCell.leftNumerator ![(11/40),0,(1/8)] ![(3/160),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(11/40),0,(1/8)] ![(3/160),1,(1/8)]) (IntegerComputedClassCell.denominator ![(11/40),0,(1/8)] ![(3/160),1,(1/8)])) := by decide +kernel
#print axioms leaf01052_transform
theorem leaf01052_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01052=true := by decide +kernel
#print axioms leaf01052_sign
theorem leaf01052_log : RationalLog.accepts (2751636489/4294967296) (-956163091/4294967296) 1 8=true := by decide +kernel
#print axioms leaf01052_log
def leaf01052 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (201699270817/500000000000) (2751636489/4294967296) (-956163091/4294967296) 1 8 ![60,0,4] ![(11/40),0,(1/8)] ![(3/160),1,(1/8)] affine01052
theorem leaf01052_checked : FastNestedCellData.accepts 1 2 4 leaf01052=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (201699270817/500000000000) (2751636489/4294967296) (-956163091/4294967296) 1 8 ![60,0,4] ![(11/40),0,(1/8)] ![(3/160),1,(1/8)] 1860347414307516330597611995136000000000000 1672654620472679741904449590084912143138816 4146407207367310662716488679424000000000000 raw01052 affine01052
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01052_raw leaf01052_rectangular
    leaf01052_transform leaf01052_sign leaf01052_log
#print axioms leaf01052_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
