/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01188 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 39762055038287956845803864064000000000000 47744061562589678194035928217058696757248 1845818590606156359971033317376000000000000))
theorem leaf01188_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 39762055038287956845803864064000000000000 47744061562589678194035928217058696757248 1845818590606156359971033317376000000000000 raw01188=true := by decide +kernel
#print axioms leaf01188_raw
theorem leaf01188_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01188=true := by decide +kernel
#print axioms leaf01188_rectangular
def affine01188 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01188 (IntegerComputedClassCell.leftNumerator ![(7/16),0,(7/8)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/16),0,(7/8)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/16),0,(7/8)] ![(1/32),1,(1/16)]))
theorem leaf01188_transform : affine01188=(NestedInteger.clearedAll 3 raw01188 (IntegerComputedClassCell.leftNumerator ![(7/16),0,(7/8)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/16),0,(7/8)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/16),0,(7/8)] ![(1/32),1,(1/16)])) := by decide +kernel
#print axioms leaf01188_transform
theorem leaf01188_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01188=true := by decide +kernel
#print axioms leaf01188_sign
theorem leaf01188_log : RationalLog.accepts (2513562807/2147483648) (169011721/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01188_log
def leaf01188 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (25866063873/1000000000000) (2513562807/2147483648) (169011721/2147483648) 0 8 ![60,0,4] ![(7/16),0,(7/8)] ![(1/32),1,(1/16)] affine01188
theorem leaf01188_checked : FastNestedCellData.accepts 1 2 4 leaf01188=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (25866063873/1000000000000) (2513562807/2147483648) (169011721/2147483648) 0 8 ![60,0,4] ![(7/16),0,(7/8)] ![(1/32),1,(1/16)] 39762055038287956845803864064000000000000 47744061562589678194035928217058696757248 1845818590606156359971033317376000000000000 raw01188 affine01188
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01188_raw leaf01188_rectangular
    leaf01188_transform leaf01188_sign leaf01188_log
#print axioms leaf01188_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
