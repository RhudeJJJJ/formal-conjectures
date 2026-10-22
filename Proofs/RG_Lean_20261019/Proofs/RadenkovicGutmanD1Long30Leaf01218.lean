/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01218 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 43210238128005924889749461401600000000000 48975125550605757281851921792836028071936 4181562732116837538045018243072000000000000))
theorem leaf01218_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 43210238128005924889749461401600000000000 48975125550605757281851921792836028071936 4181562732116837538045018243072000000000000 raw01218=true := by decide +kernel
#print axioms leaf01218_raw
theorem leaf01218_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01218=true := by decide +kernel
#print axioms leaf01218_rectangular
def affine01218 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01218 (IntegerComputedClassCell.leftNumerator ![(5/16),0,(7/8)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(5/16),0,(7/8)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.denominator ![(5/16),0,(7/8)] ![(1/64),1,(1/16)]))
theorem leaf01218_transform : affine01218=(NestedInteger.clearedAll 3 raw01218 (IntegerComputedClassCell.leftNumerator ![(5/16),0,(7/8)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(5/16),0,(7/8)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.denominator ![(5/16),0,(7/8)] ![(1/64),1,(1/16)])) := by decide +kernel
#print axioms leaf01218_transform
theorem leaf01218_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01218=true := by decide +kernel
#print axioms leaf01218_sign
theorem leaf01218_log : RationalLog.accepts (4811625195/4294967296) (121967369/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01218_log
def leaf01218 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (11712158513/1000000000000) (4811625195/4294967296) (121967369/2147483648) 0 8 ![60,0,4] ![(5/16),0,(7/8)] ![(1/64),1,(1/16)] affine01218
theorem leaf01218_checked : FastNestedCellData.accepts 1 2 4 leaf01218=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (11712158513/1000000000000) (4811625195/4294967296) (121967369/2147483648) 0 8 ![60,0,4] ![(5/16),0,(7/8)] ![(1/64),1,(1/16)] 43210238128005924889749461401600000000000 48975125550605757281851921792836028071936 4181562732116837538045018243072000000000000 raw01218 affine01218
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01218_raw leaf01218_rectangular
    leaf01218_transform leaf01218_sign leaf01218_log
#print axioms leaf01218_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
