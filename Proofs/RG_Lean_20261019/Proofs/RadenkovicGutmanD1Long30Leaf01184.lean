/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01184 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 877822365157384456379027161088000000000 1066141214069617903382055114084980883456 35846585647382398816765555507200000000000))
theorem leaf01184_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 877822365157384456379027161088000000000 1066141214069617903382055114084980883456 35846585647382398816765555507200000000000 raw01184=true := by decide +kernel
#print axioms leaf01184_raw
theorem leaf01184_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01184=true := by decide +kernel
#print axioms leaf01184_rectangular
def affine01184 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01184 (IntegerComputedClassCell.leftNumerator ![(15/32),0,(15/16)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(15/32),0,(15/16)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.denominator ![(15/32),0,(15/16)] ![(1/32),1,(1/16)]))
theorem leaf01184_transform : affine01184=(NestedInteger.clearedAll 3 raw01184 (IntegerComputedClassCell.leftNumerator ![(15/32),0,(15/16)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(15/32),0,(15/16)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.denominator ![(15/32),0,(15/16)] ![(1/32),1,(1/16)])) := by decide +kernel
#print axioms leaf01184_transform
theorem leaf01184_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01184=true := by decide +kernel
#print axioms leaf01184_sign
theorem leaf01184_log : RationalLog.accepts (5065701775/4294967296) (22152467/268435456) 0 8=true := by decide +kernel
#print axioms leaf01184_log
def leaf01184 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (5948355721/200000000000) (5065701775/4294967296) (22152467/268435456) 0 8 ![60,0,4] ![(15/32),0,(15/16)] ![(1/32),1,(1/16)] affine01184
theorem leaf01184_checked : FastNestedCellData.accepts 1 2 4 leaf01184=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (5948355721/200000000000) (5065701775/4294967296) (22152467/268435456) 0 8 ![60,0,4] ![(15/32),0,(15/16)] ![(1/32),1,(1/16)] 877822365157384456379027161088000000000 1066141214069617903382055114084980883456 35846585647382398816765555507200000000000 raw01184 affine01184
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01184_raw leaf01184_rectangular
    leaf01184_transform leaf01184_sign leaf01184_log
#print axioms leaf01184_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
