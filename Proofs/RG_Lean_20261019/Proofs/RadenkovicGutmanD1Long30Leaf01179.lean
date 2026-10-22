/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01179 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 55080770423191922669376241664000000000000 67697556297086184775669147661736672755712 1889345842831086237643433836544000000000000))
theorem leaf01179_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 55080770423191922669376241664000000000000 67697556297086184775669147661736672755712 1889345842831086237643433836544000000000000 raw01179=true := by decide +kernel
#print axioms leaf01179_raw
theorem leaf01179_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01179=true := by decide +kernel
#print axioms leaf01179_rectangular
def affine01179 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01179 (IntegerComputedClassCell.leftNumerator ![(1/2),0,(15/16)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/2),0,(15/16)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/2),0,(15/16)] ![(1/16),1,(1/16)]))
theorem leaf01179_transform : affine01179=(NestedInteger.clearedAll 3 raw01179 (IntegerComputedClassCell.leftNumerator ![(1/2),0,(15/16)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/2),0,(15/16)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/2),0,(15/16)] ![(1/16),1,(1/16)])) := by decide +kernel
#print axioms leaf01179_transform
theorem leaf01179_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01179=true := by decide +kernel
#print axioms leaf01179_sign
theorem leaf01179_log : RationalLog.accepts (2548084683/2147483648) (367316795/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01179_log
def leaf01179 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (35831214573/1000000000000) (2548084683/2147483648) (367316795/4294967296) 0 8 ![60,0,4] ![(1/2),0,(15/16)] ![(1/16),1,(1/16)] affine01179
theorem leaf01179_checked : FastNestedCellData.accepts 1 2 4 leaf01179=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (35831214573/1000000000000) (2548084683/2147483648) (367316795/4294967296) 0 8 ![60,0,4] ![(1/2),0,(15/16)] ![(1/16),1,(1/16)] 55080770423191922669376241664000000000000 67697556297086184775669147661736672755712 1889345842831086237643433836544000000000000 raw01179 affine01179
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01179_raw leaf01179_rectangular
    leaf01179_transform leaf01179_sign leaf01179_log
#print axioms leaf01179_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
