/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01194 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 6389194736215228340116652032000000000000 7575609787632178911630020389033356558336 341752121952267461488187277312000000000000))
theorem leaf01194_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 6389194736215228340116652032000000000000 7575609787632178911630020389033356558336 341752121952267461488187277312000000000000 raw01194=true := by decide +kernel
#print axioms leaf01194_raw
theorem leaf01194_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01194=true := by decide +kernel
#print axioms leaf01194_rectangular
def affine01194 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01194 (IntegerComputedClassCell.leftNumerator ![(13/32),0,(15/16)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/32),0,(15/16)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/32),0,(15/16)] ![(1/32),1,(1/16)]))
theorem leaf01194_transform : affine01194=(NestedInteger.clearedAll 3 raw01194 (IntegerComputedClassCell.leftNumerator ![(13/32),0,(15/16)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/32),0,(15/16)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/32),0,(15/16)] ![(1/32),1,(1/16)])) := by decide +kernel
#print axioms leaf01194_transform
theorem leaf01194_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01194=true := by decide +kernel
#print axioms leaf01194_sign
theorem leaf01194_log : RationalLog.accepts (622758267/536870912) (318688185/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01194_log
def leaf01194 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (22166972203/1000000000000) (622758267/536870912) (318688185/4294967296) 0 8 ![60,0,4] ![(13/32),0,(15/16)] ![(1/32),1,(1/16)] affine01194
theorem leaf01194_checked : FastNestedCellData.accepts 1 2 4 leaf01194=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (22166972203/1000000000000) (622758267/536870912) (318688185/4294967296) 0 8 ![60,0,4] ![(13/32),0,(15/16)] ![(1/32),1,(1/16)] 6389194736215228340116652032000000000000 7575609787632178911630020389033356558336 341752121952267461488187277312000000000000 raw01194 affine01194
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01194_raw leaf01194_rectangular
    leaf01194_transform leaf01194_sign leaf01194_log
#print axioms leaf01194_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
