/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01289 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 33576690496565771392516096000000000000 35029998578091142562755434394222067712 18794120112488882798799618048000000000000))
theorem leaf01289_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 33576690496565771392516096000000000000 35029998578091142562755434394222067712 18794120112488882798799618048000000000000 raw01289=true := by decide +kernel
#print axioms leaf01289_raw
theorem leaf01289_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01289=true := by decide +kernel
#print axioms leaf01289_rectangular
def affine01289 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01289 (IntegerComputedClassCell.leftNumerator ![(5/32),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(5/32),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(5/32),0,(15/16)] ![(1/128),1,(1/16)]))
theorem leaf01289_transform : affine01289=(NestedInteger.clearedAll 3 raw01289 (IntegerComputedClassCell.leftNumerator ![(5/32),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(5/32),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(5/32),0,(15/16)] ![(1/128),1,(1/16)])) := by decide +kernel
#print axioms leaf01289_transform
theorem leaf01289_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01289=true := by decide +kernel
#print axioms leaf01289_sign
theorem leaf01289_log : RationalLog.accepts (1118132787/1073741824) (21748941/1073741824) 0 8=true := by decide +kernel
#print axioms leaf01289_log
def leaf01289 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (232985093/125000000000) (1118132787/1073741824) (21748941/1073741824) 0 8 ![60,0,4] ![(5/32),0,(15/16)] ![(1/128),1,(1/16)] affine01289
theorem leaf01289_checked : FastNestedCellData.accepts 1 2 4 leaf01289=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (232985093/125000000000) (1118132787/1073741824) (21748941/1073741824) 0 8 ![60,0,4] ![(5/32),0,(15/16)] ![(1/128),1,(1/16)] 33576690496565771392516096000000000000 35029998578091142562755434394222067712 18794120112488882798799618048000000000000 raw01289 affine01289
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01289_raw leaf01289_rectangular
    leaf01289_transform leaf01289_sign leaf01289_log
#print axioms leaf01289_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
