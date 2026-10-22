/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01253 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 21479751277948450294359654400000000000 23045101518173400725373861808903815168 5497517229618634657610543923200000000000))
theorem leaf01253_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 21479751277948450294359654400000000000 23045101518173400725373861808903815168 5497517229618634657610543923200000000000 raw01253=true := by decide +kernel
#print axioms leaf01253_raw
theorem leaf01253_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01253=true := by decide +kernel
#print axioms leaf01253_rectangular
def affine01253 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01253 (IntegerComputedClassCell.leftNumerator ![(27/128),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(27/128),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(27/128),0,(7/8)] ![(1/128),1,(1/16)]))
theorem leaf01253_transform : affine01253=(NestedInteger.clearedAll 3 raw01253 (IntegerComputedClassCell.leftNumerator ![(27/128),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(27/128),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(27/128),0,(7/8)] ![(1/128),1,(1/16)])) := by decide +kernel
#print axioms leaf01253_transform
theorem leaf01253_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01253=true := by decide +kernel
#print axioms leaf01253_sign
theorem leaf01253_log : RationalLog.accepts (4588730163/4294967296) (35519053/1073741824) 0 8=true := by decide +kernel
#print axioms leaf01253_log
def leaf01253 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (209595537/50000000000) (4588730163/4294967296) (35519053/1073741824) 0 8 ![60,0,4] ![(27/128),0,(7/8)] ![(1/128),1,(1/16)] affine01253
theorem leaf01253_checked : FastNestedCellData.accepts 1 2 4 leaf01253=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (209595537/50000000000) (4588730163/4294967296) (35519053/1073741824) 0 8 ![60,0,4] ![(27/128),0,(7/8)] ![(1/128),1,(1/16)] 21479751277948450294359654400000000000 23045101518173400725373861808903815168 5497517229618634657610543923200000000000 raw01253 affine01253
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01253_raw leaf01253_rectangular
    leaf01253_transform leaf01253_sign leaf01253_log
#print axioms leaf01253_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
