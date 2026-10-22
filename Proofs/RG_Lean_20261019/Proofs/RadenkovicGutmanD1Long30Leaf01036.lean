/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01036 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 58596494069328559057756225536000000000000 45104761700168721305846529777352166080512 91021897453044242439064256512000000000000))
theorem leaf01036_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 58596494069328559057756225536000000000000 45104761700168721305846529777352166080512 91021897453044242439064256512000000000000 raw01036=true := by decide +kernel
#print axioms leaf01036_raw
theorem leaf01036_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01036=true := by decide +kernel
#print axioms leaf01036_rectangular
def affine01036 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01036 (IntegerComputedClassCell.leftNumerator ![(7/32),0,(1/16)] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/32),0,(1/16)] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/32),0,(1/16)] ![(3/160),1,(1/16)]))
theorem leaf01036_transform : affine01036=(NestedInteger.clearedAll 3 raw01036 (IntegerComputedClassCell.leftNumerator ![(7/32),0,(1/16)] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/32),0,(1/16)] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/32),0,(1/16)] ![(3/160),1,(1/16)])) := by decide +kernel
#print axioms leaf01036_transform
theorem leaf01036_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01036=true := by decide +kernel
#print axioms leaf01036_sign
theorem leaf01036_log : RationalLog.accepts (2210616057/4294967296) (-356575015/1073741824) 1 8=true := by decide +kernel
#print axioms leaf01036_log
def leaf01036 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (247768740063/500000000000) (2210616057/4294967296) (-356575015/1073741824) 1 8 ![60,0,4] ![(7/32),0,(1/16)] ![(3/160),1,(1/16)] affine01036
theorem leaf01036_checked : FastNestedCellData.accepts 1 2 4 leaf01036=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (247768740063/500000000000) (2210616057/4294967296) (-356575015/1073741824) 1 8 ![60,0,4] ![(7/32),0,(1/16)] ![(3/160),1,(1/16)] 58596494069328559057756225536000000000000 45104761700168721305846529777352166080512 91021897453044242439064256512000000000000 raw01036 affine01036
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01036_raw leaf01036_rectangular
    leaf01036_transform leaf01036_sign leaf01036_log
#print axioms leaf01036_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
