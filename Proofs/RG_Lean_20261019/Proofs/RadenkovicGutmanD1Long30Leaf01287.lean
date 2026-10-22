/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01287 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 2148908195238973882941571072000000000000 2241919912613017432660133605412953915392 1202823687202890256937738305536000000000000))
theorem leaf01287_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 2148908195238973882941571072000000000000 2241919912613017432660133605412953915392 1202823687202890256937738305536000000000000 raw01287=true := by decide +kernel
#print axioms leaf01287_raw
theorem leaf01287_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01287=true := by decide +kernel
#print axioms leaf01287_rectangular
def affine01287 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01287 (IntegerComputedClassCell.leftNumerator ![(5/32),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(5/32),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.denominator ![(5/32),0,(3/4)] ![(1/128),1,(1/8)]))
theorem leaf01287_transform : affine01287=(NestedInteger.clearedAll 3 raw01287 (IntegerComputedClassCell.leftNumerator ![(5/32),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(5/32),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.denominator ![(5/32),0,(3/4)] ![(1/128),1,(1/8)])) := by decide +kernel
#print axioms leaf01287_transform
theorem leaf01287_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01287=true := by decide +kernel
#print axioms leaf01287_sign
theorem leaf01287_log : RationalLog.accepts (1118132787/1073741824) (21748941/1073741824) 0 8=true := by decide +kernel
#print axioms leaf01287_log
def leaf01287 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (1863880747/1000000000000) (1118132787/1073741824) (21748941/1073741824) 0 8 ![60,0,4] ![(5/32),0,(3/4)] ![(1/128),1,(1/8)] affine01287
theorem leaf01287_checked : FastNestedCellData.accepts 1 2 4 leaf01287=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (1863880747/1000000000000) (1118132787/1073741824) (21748941/1073741824) 0 8 ![60,0,4] ![(5/32),0,(3/4)] ![(1/128),1,(1/8)] 2148908195238973882941571072000000000000 2241919912613017432660133605412953915392 1202823687202890256937738305536000000000000 raw01287 affine01287
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01287_raw leaf01287_rectangular
    leaf01287_transform leaf01287_sign leaf01287_log
#print axioms leaf01287_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
