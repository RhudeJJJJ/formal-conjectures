/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01207 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 900058295182070255826711347200000000000 1036354334265537012048009146524986507264 70800462874495646089689327206400000000000))
theorem leaf01207_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 900058295182070255826711347200000000000 1036354334265537012048009146524986507264 70800462874495646089689327206400000000000 raw01207=true := by decide +kernel
#print axioms leaf01207_raw
theorem leaf01207_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01207=true := by decide +kernel
#print axioms leaf01207_rectangular
def affine01207 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01207 (IntegerComputedClassCell.leftNumerator ![(11/32),0,(3/4)] ![(1/64),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(11/32),0,(3/4)] ![(1/64),1,(1/8)]) (IntegerComputedClassCell.denominator ![(11/32),0,(3/4)] ![(1/64),1,(1/8)]))
theorem leaf01207_transform : affine01207=(NestedInteger.clearedAll 3 raw01207 (IntegerComputedClassCell.leftNumerator ![(11/32),0,(3/4)] ![(1/64),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(11/32),0,(3/4)] ![(1/64),1,(1/8)]) (IntegerComputedClassCell.denominator ![(11/32),0,(3/4)] ![(1/64),1,(1/8)])) := by decide +kernel
#print axioms leaf01207_transform
theorem leaf01207_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01207=true := by decide +kernel
#print axioms leaf01207_sign
theorem leaf01207_log : RationalLog.accepts (2437005501/2147483648) (135799641/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01207_log
def leaf01207 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (2927535477/200000000000) (2437005501/2147483648) (135799641/2147483648) 0 8 ![60,0,4] ![(11/32),0,(3/4)] ![(1/64),1,(1/8)] affine01207
theorem leaf01207_checked : FastNestedCellData.accepts 1 2 4 leaf01207=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (2927535477/200000000000) (2437005501/2147483648) (135799641/2147483648) 0 8 ![60,0,4] ![(11/32),0,(3/4)] ![(1/64),1,(1/8)] 900058295182070255826711347200000000000 1036354334265537012048009146524986507264 70800462874495646089689327206400000000000 raw01207 affine01207
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01207_raw leaf01207_rectangular
    leaf01207_transform leaf01207_sign leaf01207_log
#print axioms leaf01207_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
