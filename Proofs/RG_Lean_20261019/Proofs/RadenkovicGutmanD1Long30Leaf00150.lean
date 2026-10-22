/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00150 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 69969094016009492565140386611200000000000 14475752255513221730745105485437861888 47705079808303911348994048000000000000))
theorem leaf00150_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 69969094016009492565140386611200000000000 14475752255513221730745105485437861888 47705079808303911348994048000000000000 raw00150=true := by decide +kernel
#print axioms leaf00150_raw
theorem leaf00150_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00150=true := by decide +kernel
#print axioms leaf00150_rectangular
def affine00150 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00150 (IntegerComputedClassCell.leftNumerator ![(53/16000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(53/16000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(53/16000),0,0] ![(3/32000),1,(1/16)]))
theorem leaf00150_transform : affine00150=(NestedInteger.clearedAll 3 raw00150 (IntegerComputedClassCell.leftNumerator ![(53/16000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(53/16000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(53/16000),0,0] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00150_transform
theorem leaf00150_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00150=true := by decide +kernel
#print axioms leaf00150_sign
theorem leaf00150_log : RationalLog.accepts (681715/4294967296) (-18786923605/4294967296) 13 8=true := by decide +kernel
#print axioms leaf00150_log
def leaf00150 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (75860643739/250000000000) (681715/4294967296) (-18786923605/4294967296) 13 8 ![60,0,4] ![(53/16000),0,0] ![(3/32000),1,(1/16)] affine00150
theorem leaf00150_checked : FastNestedCellData.accepts 1 2 4 leaf00150=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (75860643739/250000000000) (681715/4294967296) (-18786923605/4294967296) 13 8 ![60,0,4] ![(53/16000),0,0] ![(3/32000),1,(1/16)] 69969094016009492565140386611200000000000 14475752255513221730745105485437861888 47705079808303911348994048000000000000 raw00150 affine00150
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00150_raw leaf00150_rectangular
    leaf00150_transform leaf00150_sign leaf00150_log
#print axioms leaf00150_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
