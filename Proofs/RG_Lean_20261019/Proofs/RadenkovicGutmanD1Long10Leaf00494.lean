/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00494 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 3128130837650893959069696000000000000 3129653122858403975556378989980286976 1153482566609356176867412934656000000000000))
theorem leaf00494_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 3128130837650893959069696000000000000 3129653122858403975556378989980286976 1153482566609356176867412934656000000000000 raw00494=true := by decide +kernel
#print axioms leaf00494_raw
theorem leaf00494_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00494=true := by decide +kernel
#print axioms leaf00494_rectangular
def affine00494 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00494 (IntegerComputedClassCell.leftNumerator ![(1/64),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.widthNumerator ![(1/64),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.denominator ![(1/64),0,0] ![(1/256),1,1]))
theorem leaf00494_transform : affine00494=(NestedInteger.clearedAll 3 raw00494 (IntegerComputedClassCell.leftNumerator ![(1/64),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.widthNumerator ![(1/64),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.denominator ![(1/64),0,0] ![(1/256),1,1])) := by decide +kernel
#print axioms leaf00494_transform
theorem leaf00494_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00494=true := by decide +kernel
#print axioms leaf00494_sign
theorem leaf00494_log : RationalLog.accepts (1074261439/1073741824) (519489/2147483648) 0 8=true := by decide +kernel
#print axioms leaf00494_log
def leaf00494 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (2713221/1000000000000) (1074261439/1073741824) (519489/2147483648) 0 8 ![52,0,4] ![(1/64),0,0] ![(1/256),1,1] affine00494
theorem leaf00494_checked : FastNestedCellData.accepts 1 0 4 leaf00494=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (2713221/1000000000000) (1074261439/1073741824) (519489/2147483648) 0 8 ![52,0,4] ![(1/64),0,0] ![(1/256),1,1] 3128130837650893959069696000000000000 3129653122858403975556378989980286976 1153482566609356176867412934656000000000000 raw00494 affine00494
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00494_raw leaf00494_rectangular
    leaf00494_transform leaf00494_sign leaf00494_log
#print axioms leaf00494_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
