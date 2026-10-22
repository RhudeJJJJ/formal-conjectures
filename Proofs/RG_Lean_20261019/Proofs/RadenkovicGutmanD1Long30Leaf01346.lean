/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01346 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 9877483781875727350104064000000000000 9907213647434271348695370265503203328 289097909880149990014281842688000000000000))
theorem leaf01346_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 9877483781875727350104064000000000000 9907213647434271348695370265503203328 289097909880149990014281842688000000000000 raw01346=true := by decide +kernel
#print axioms leaf01346_raw
theorem leaf01346_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01346=true := by decide +kernel
#print axioms leaf01346_rectangular
def affine01346 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01346 (IntegerComputedClassCell.leftNumerator ![(5/128),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.widthNumerator ![(5/128),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.denominator ![(5/128),0,0] ![(1/256),1,1]))
theorem leaf01346_transform : affine01346=(NestedInteger.clearedAll 3 raw01346 (IntegerComputedClassCell.leftNumerator ![(5/128),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.widthNumerator ![(5/128),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.denominator ![(5/128),0,0] ![(1/256),1,1])) := by decide +kernel
#print axioms leaf01346_transform
theorem leaf01346_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01346=true := by decide +kernel
#print axioms leaf01346_sign
theorem leaf01346_log : RationalLog.accepts (1076936733/1073741824) (3190165/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01346_log
def leaf01346 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (17134703/500000000000) (1076936733/1073741824) (3190165/2147483648) 0 8 ![60,0,4] ![(5/128),0,0] ![(1/256),1,1] affine01346
theorem leaf01346_checked : FastNestedCellData.accepts 1 2 4 leaf01346=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (17134703/500000000000) (1076936733/1073741824) (3190165/2147483648) 0 8 ![60,0,4] ![(5/128),0,0] ![(1/256),1,1] 9877483781875727350104064000000000000 9907213647434271348695370265503203328 289097909880149990014281842688000000000000 raw01346 affine01346
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01346_raw leaf01346_rectangular
    leaf01346_transform leaf01346_sign leaf01346_log
#print axioms leaf01346_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
