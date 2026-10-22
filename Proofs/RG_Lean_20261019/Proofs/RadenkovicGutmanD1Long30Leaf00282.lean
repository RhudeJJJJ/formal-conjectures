/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00282 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 28135930998176307606085173248000000000000 22548960480343226822875312740765819469824 230996278797409517130819305472000000000000))
theorem leaf00282_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 28135930998176307606085173248000000000000 22548960480343226822875312740765819469824 230996278797409517130819305472000000000000 raw00282=true := by decide +kernel
#print axioms leaf00282_raw
theorem leaf00282_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00282=true := by decide +kernel
#print axioms leaf00282_rectangular
def affine00282 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00282 (IntegerComputedClassCell.leftNumerator ![(1/160),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(1/160),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(1/160),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00282_transform : affine00282=(NestedInteger.clearedAll 3 raw00282 (IntegerComputedClassCell.leftNumerator ![(1/160),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(1/160),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(1/160),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00282_transform
theorem leaf00282_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00282=true := by decide +kernel
#print axioms leaf00282_sign
theorem leaf00282_log : RationalLog.accepts (783997411/1073741824) (-337690899/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00282_log
def leaf00282 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (48808060021/500000000000) (783997411/1073741824) (-337690899/2147483648) 1 8 ![60,0,4] ![(1/160),0,(1/8)] ![(1/6400),1,(1/8)] affine00282
theorem leaf00282_checked : FastNestedCellData.accepts 1 2 4 leaf00282=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (48808060021/500000000000) (783997411/1073741824) (-337690899/2147483648) 1 8 ![60,0,4] ![(1/160),0,(1/8)] ![(1/6400),1,(1/8)] 28135930998176307606085173248000000000000 22548960480343226822875312740765819469824 230996278797409517130819305472000000000000 raw00282 affine00282
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00282_raw leaf00282_rectangular
    leaf00282_transform leaf00282_sign leaf00282_log
#print axioms leaf00282_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
