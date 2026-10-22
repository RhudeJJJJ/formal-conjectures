/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00407 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 535758980982641528201635954688000000000000 736915066113879356074974956716287634440192 6343189806977738165173811675136000000000000))
theorem leaf00407_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 535758980982641528201635954688000000000000 736915066113879356074974956716287634440192 6343189806977738165173811675136000000000000 raw00407=true := by decide +kernel
#print axioms leaf00407_raw
theorem leaf00407_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00407=true := by decide +kernel
#print axioms leaf00407_rectangular
def affine00407 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00407 (IntegerComputedClassCell.leftNumerator ![(7/8),0,(3/4)] ![(1/8),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/8),0,(3/4)] ![(1/8),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/8),0,(3/4)] ![(1/8),1,(1/4)]))
theorem leaf00407_transform : affine00407=(NestedInteger.clearedAll 3 raw00407 (IntegerComputedClassCell.leftNumerator ![(7/8),0,(3/4)] ![(1/8),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/8),0,(3/4)] ![(1/8),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/8),0,(3/4)] ![(1/8),1,(1/4)])) := by decide +kernel
#print axioms leaf00407_transform
theorem leaf00407_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00407=true := by decide +kernel
#print axioms leaf00407_sign
theorem leaf00407_log : RationalLog.accepts (5292682637/4294967296) (448569157/4294967296) 0 8=true := by decide +kernel
#print axioms leaf00407_log
def leaf00407 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (58087105111/500000000000) (5292682637/4294967296) (448569157/4294967296) 0 8 ![52,0,4] ![(7/8),0,(3/4)] ![(1/8),1,(1/4)] affine00407
theorem leaf00407_checked : FastNestedCellData.accepts 1 0 4 leaf00407=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (58087105111/500000000000) (5292682637/4294967296) (448569157/4294967296) 0 8 ![52,0,4] ![(7/8),0,(3/4)] ![(1/8),1,(1/4)] 535758980982641528201635954688000000000000 736915066113879356074974956716287634440192 6343189806977738165173811675136000000000000 raw00407 affine00407
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00407_raw leaf00407_rectangular
    leaf00407_transform leaf00407_sign leaf00407_log
#print axioms leaf00407_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
