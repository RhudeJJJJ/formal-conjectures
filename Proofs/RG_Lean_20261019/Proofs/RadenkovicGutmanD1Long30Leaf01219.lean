/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01219 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 54012781818865932814109376512000000000000 61218887045475299377553686726653713055744 5226953249660113438053444354048000000000000))
theorem leaf01219_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 54012781818865932814109376512000000000000 61218887045475299377553686726653713055744 5226953249660113438053444354048000000000000 raw01219=true := by decide +kernel
#print axioms leaf01219_raw
theorem leaf01219_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01219=true := by decide +kernel
#print axioms leaf01219_rectangular
def affine01219 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01219 (IntegerComputedClassCell.leftNumerator ![(5/16),0,(15/16)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(5/16),0,(15/16)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.denominator ![(5/16),0,(15/16)] ![(1/64),1,(1/16)]))
theorem leaf01219_transform : affine01219=(NestedInteger.clearedAll 3 raw01219 (IntegerComputedClassCell.leftNumerator ![(5/16),0,(15/16)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(5/16),0,(15/16)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.denominator ![(5/16),0,(15/16)] ![(1/64),1,(1/16)])) := by decide +kernel
#print axioms leaf01219_transform
theorem leaf01219_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01219=true := by decide +kernel
#print axioms leaf01219_sign
theorem leaf01219_log : RationalLog.accepts (4811625059/4294967296) (121967339/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01219_log
def leaf01219 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (5856077539/500000000000) (4811625059/4294967296) (121967339/2147483648) 0 8 ![60,0,4] ![(5/16),0,(15/16)] ![(1/64),1,(1/16)] affine01219
theorem leaf01219_checked : FastNestedCellData.accepts 1 2 4 leaf01219=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (5856077539/500000000000) (4811625059/4294967296) (121967339/2147483648) 0 8 ![60,0,4] ![(5/16),0,(15/16)] ![(1/64),1,(1/16)] 54012781818865932814109376512000000000000 61218887045475299377553686726653713055744 5226953249660113438053444354048000000000000 raw01219 affine01219
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01219_raw leaf01219_rectangular
    leaf01219_transform leaf01219_sign leaf01219_log
#print axioms leaf01219_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
