/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01189 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 119285605117830652899698409472000000000000 143231407224024326843274060658160143695872 5537451710474461711198746312704000000000000))
theorem leaf01189_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 119285605117830652899698409472000000000000 143231407224024326843274060658160143695872 5537451710474461711198746312704000000000000 raw01189=true := by decide +kernel
#print axioms leaf01189_raw
theorem leaf01189_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01189=true := by decide +kernel
#print axioms leaf01189_rectangular
def affine01189 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01189 (IntegerComputedClassCell.leftNumerator ![(7/16),0,(15/16)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/16),0,(15/16)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/16),0,(15/16)] ![(1/32),1,(1/16)]))
theorem leaf01189_transform : affine01189=(NestedInteger.clearedAll 3 raw01189 (IntegerComputedClassCell.leftNumerator ![(7/16),0,(15/16)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/16),0,(15/16)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/16),0,(15/16)] ![(1/32),1,(1/16)])) := by decide +kernel
#print axioms leaf01189_transform
theorem leaf01189_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01189=true := by decide +kernel
#print axioms leaf01189_sign
theorem leaf01189_log : RationalLog.accepts (2513561261/2147483648) (338022121/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01189_log
def leaf01189 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (25865942443/1000000000000) (2513561261/2147483648) (338022121/4294967296) 0 8 ![60,0,4] ![(7/16),0,(15/16)] ![(1/32),1,(1/16)] affine01189
theorem leaf01189_checked : FastNestedCellData.accepts 1 2 4 leaf01189=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (25865942443/1000000000000) (2513561261/2147483648) (338022121/4294967296) 0 8 ![60,0,4] ![(7/16),0,(15/16)] ![(1/32),1,(1/16)] 119285605117830652899698409472000000000000 143231407224024326843274060658160143695872 5537451710474461711198746312704000000000000 raw01189 affine01189
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01189_raw leaf01189_rectangular
    leaf01189_transform leaf01189_sign leaf01189_log
#print axioms leaf01189_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
