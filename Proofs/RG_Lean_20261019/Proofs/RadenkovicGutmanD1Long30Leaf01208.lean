/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01208 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 16876076897221517314713714688000000000000 19431623550812549137155610602181205426176 1327508567162615034794897047552000000000000))
theorem leaf01208_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 16876076897221517314713714688000000000000 19431623550812549137155610602181205426176 1327508567162615034794897047552000000000000 raw01208=true := by decide +kernel
#print axioms leaf01208_raw
theorem leaf01208_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01208=true := by decide +kernel
#print axioms leaf01208_rectangular
def affine01208 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01208 (IntegerComputedClassCell.leftNumerator ![(11/32),0,(7/8)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/32),0,(7/8)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/32),0,(7/8)] ![(1/64),1,(1/16)]))
theorem leaf01208_transform : affine01208=(NestedInteger.clearedAll 3 raw01208 (IntegerComputedClassCell.leftNumerator ![(11/32),0,(7/8)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/32),0,(7/8)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/32),0,(7/8)] ![(1/64),1,(1/16)])) := by decide +kernel
#print axioms leaf01208_transform
theorem leaf01208_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01208=true := by decide +kernel
#print axioms leaf01208_sign
theorem leaf01208_log : RationalLog.accepts (4874010659/4294967296) (271599131/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01208_log
def leaf01208 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (3659415847/250000000000) (4874010659/4294967296) (271599131/4294967296) 0 8 ![60,0,4] ![(11/32),0,(7/8)] ![(1/64),1,(1/16)] affine01208
theorem leaf01208_checked : FastNestedCellData.accepts 1 2 4 leaf01208=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (3659415847/250000000000) (4874010659/4294967296) (271599131/4294967296) 0 8 ![60,0,4] ![(11/32),0,(7/8)] ![(1/64),1,(1/16)] 16876076897221517314713714688000000000000 19431623550812549137155610602181205426176 1327508567162615034794897047552000000000000 raw01208 affine01208
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01208_raw leaf01208_rectangular
    leaf01208_transform leaf01208_sign leaf01208_log
#print axioms leaf01208_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
