/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01022 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2348331685642366112231359250432000000000000 1636601877288478818130769577361864315109376 3213981245225476198776252137472000000000000))
theorem leaf01022_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2348331685642366112231359250432000000000000 1636601877288478818130769577361864315109376 3213981245225476198776252137472000000000000 raw01022=true := by decide +kernel
#print axioms leaf01022_raw
theorem leaf01022_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01022=true := by decide +kernel
#print axioms leaf01022_rectangular
def affine01022 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01022 (IntegerComputedClassCell.leftNumerator ![(3/16),0,(1/8)] ![(1/80),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(3/16),0,(1/8)] ![(1/80),1,(1/8)]) (IntegerComputedClassCell.denominator ![(3/16),0,(1/8)] ![(1/80),1,(1/8)]))
theorem leaf01022_transform : affine01022=(NestedInteger.clearedAll 3 raw01022 (IntegerComputedClassCell.leftNumerator ![(3/16),0,(1/8)] ![(1/80),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(3/16),0,(1/8)] ![(1/80),1,(1/8)]) (IntegerComputedClassCell.denominator ![(3/16),0,(1/8)] ![(1/80),1,(1/8)])) := by decide +kernel
#print axioms leaf01022_transform
theorem leaf01022_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01022=true := by decide +kernel
#print axioms leaf01022_sign
theorem leaf01022_log : RationalLog.accepts (1983320291/4294967296) (-414824917/1073741824) 2 8=true := by decide +kernel
#print axioms leaf01022_log
def leaf01022 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (254606631529/500000000000) (1983320291/4294967296) (-414824917/1073741824) 2 8 ![60,0,4] ![(3/16),0,(1/8)] ![(1/80),1,(1/8)] affine01022
theorem leaf01022_checked : FastNestedCellData.accepts 1 2 4 leaf01022=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (254606631529/500000000000) (1983320291/4294967296) (-414824917/1073741824) 2 8 ![60,0,4] ![(3/16),0,(1/8)] ![(1/80),1,(1/8)] 2348331685642366112231359250432000000000000 1636601877288478818130769577361864315109376 3213981245225476198776252137472000000000000 raw01022 affine01022
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01022_raw leaf01022_rectangular
    leaf01022_transform leaf01022_sign leaf01022_log
#print axioms leaf01022_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
