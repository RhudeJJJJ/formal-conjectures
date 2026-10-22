/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01248 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 696506941153630885506973696000000000 750554162979578705975733368037310464 155298171443577861332533248000000000000))
theorem leaf01248_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 696506941153630885506973696000000000 750554162979578705975733368037310464 155298171443577861332533248000000000000 raw01248=true := by decide +kernel
#print axioms leaf01248_raw
theorem leaf01248_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01248=true := by decide +kernel
#print axioms leaf01248_rectangular
def affine01248 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01248 (IntegerComputedClassCell.leftNumerator ![(7/32),0,(7/8)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/32),0,(7/8)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/32),0,(7/8)] ![(1/64),1,(1/16)]))
theorem leaf01248_transform : affine01248=(NestedInteger.clearedAll 3 raw01248 (IntegerComputedClassCell.leftNumerator ![(7/32),0,(7/8)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/32),0,(7/8)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/32),0,(7/8)] ![(1/64),1,(1/16)])) := by decide +kernel
#print axioms leaf01248_transform
theorem leaf01248_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01248=true := by decide +kernel
#print axioms leaf01248_sign
theorem leaf01248_log : RationalLog.accepts (1151496375/1073741824) (75068203/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01248_log
def leaf01248 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (604123471/125000000000) (1151496375/1073741824) (75068203/2147483648) 0 8 ![60,0,4] ![(7/32),0,(7/8)] ![(1/64),1,(1/16)] affine01248
theorem leaf01248_checked : FastNestedCellData.accepts 1 2 4 leaf01248=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (604123471/125000000000) (1151496375/1073741824) (75068203/2147483648) 0 8 ![60,0,4] ![(7/32),0,(7/8)] ![(1/64),1,(1/16)] 696506941153630885506973696000000000 750554162979578705975733368037310464 155298171443577861332533248000000000000 raw01248 affine01248
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01248_raw leaf01248_rectangular
    leaf01248_transform leaf01248_sign leaf01248_log
#print axioms leaf01248_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
