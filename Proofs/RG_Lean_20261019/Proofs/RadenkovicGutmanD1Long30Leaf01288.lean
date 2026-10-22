/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01288 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 85956327717325234949115084800000000000 89676796408115782409141675896590041088 48112947488019563402454525542400000000000))
theorem leaf01288_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 85956327717325234949115084800000000000 89676796408115782409141675896590041088 48112947488019563402454525542400000000000 raw01288=true := by decide +kernel
#print axioms leaf01288_raw
theorem leaf01288_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01288=true := by decide +kernel
#print axioms leaf01288_rectangular
def affine01288 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01288 (IntegerComputedClassCell.leftNumerator ![(5/32),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(5/32),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(5/32),0,(7/8)] ![(1/128),1,(1/16)]))
theorem leaf01288_transform : affine01288=(NestedInteger.clearedAll 3 raw01288 (IntegerComputedClassCell.leftNumerator ![(5/32),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(5/32),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(5/32),0,(7/8)] ![(1/128),1,(1/16)])) := by decide +kernel
#print axioms leaf01288_transform
theorem leaf01288_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01288=true := by decide +kernel
#print axioms leaf01288_sign
theorem leaf01288_log : RationalLog.accepts (1118132787/1073741824) (21748941/1073741824) 0 8=true := by decide +kernel
#print axioms leaf01288_log
def leaf01288 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (372776149/200000000000) (1118132787/1073741824) (21748941/1073741824) 0 8 ![60,0,4] ![(5/32),0,(7/8)] ![(1/128),1,(1/16)] affine01288
theorem leaf01288_checked : FastNestedCellData.accepts 1 2 4 leaf01288=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (372776149/200000000000) (1118132787/1073741824) (21748941/1073741824) 0 8 ![60,0,4] ![(5/32),0,(7/8)] ![(1/128),1,(1/16)] 85956327717325234949115084800000000000 89676796408115782409141675896590041088 48112947488019563402454525542400000000000 raw01288 affine01288
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01288_raw leaf01288_rectangular
    leaf01288_transform leaf01288_sign leaf01288_log
#print axioms leaf01288_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
