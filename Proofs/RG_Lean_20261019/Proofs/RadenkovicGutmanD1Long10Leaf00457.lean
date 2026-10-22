/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00457 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 3051650975680216512482770944000000000000 3213015054137766041460546513485810368512 1213885264095530556625831067648000000000000))
theorem leaf00457_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 3051650975680216512482770944000000000000 3213015054137766041460546513485810368512 1213885264095530556625831067648000000000000 raw00457=true := by decide +kernel
#print axioms leaf00457_raw
theorem leaf00457_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00457=true := by decide +kernel
#print axioms leaf00457_rectangular
def affine00457 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00457 (IntegerComputedClassCell.leftNumerator ![(11/64),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/64),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/64),0,(1/2)] ![(1/64),1,(1/4)]))
theorem leaf00457_transform : affine00457=(NestedInteger.clearedAll 3 raw00457 (IntegerComputedClassCell.leftNumerator ![(11/64),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/64),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/64),0,(1/2)] ![(1/64),1,(1/4)])) := by decide +kernel
#print axioms leaf00457_transform
theorem leaf00457_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00457=true := by decide +kernel
#print axioms leaf00457_sign
theorem leaf00457_log : RationalLog.accepts (2255068591/2147483648) (52488397/2147483648) 0 8=true := by decide +kernel
#print axioms leaf00457_log
def leaf00457 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (1323442647/500000000000) (2255068591/2147483648) (52488397/2147483648) 0 8 ![52,0,4] ![(11/64),0,(1/2)] ![(1/64),1,(1/4)] affine00457
theorem leaf00457_checked : FastNestedCellData.accepts 1 0 4 leaf00457=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (1323442647/500000000000) (2255068591/2147483648) (52488397/2147483648) 0 8 ![52,0,4] ![(11/64),0,(1/2)] ![(1/64),1,(1/4)] 3051650975680216512482770944000000000000 3213015054137766041460546513485810368512 1213885264095530556625831067648000000000000 raw00457 affine00457
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00457_raw leaf00457_rectangular
    leaf00457_transform leaf00457_sign leaf00457_log
#print axioms leaf00457_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
