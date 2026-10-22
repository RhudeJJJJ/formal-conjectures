/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00187 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 14892083652383448052304707584000000000000 9658902186468867009044810230610352144384 46736055803261296840735195136000000000000))
theorem leaf00187_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 14892083652383448052304707584000000000000 9658902186468867009044810230610352144384 46736055803261296840735195136000000000000 raw00187=true := by decide +kernel
#print axioms leaf00187_raw
theorem leaf00187_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00187=true := by decide +kernel
#print axioms leaf00187_rectangular
def affine00187 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00187 (IntegerComputedClassCell.leftNumerator ![(91/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(91/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(91/3200),0,(1/4)] ![(3/3200),1,(1/4)]))
theorem leaf00187_transform : affine00187=(NestedInteger.clearedAll 3 raw00187 (IntegerComputedClassCell.leftNumerator ![(91/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(91/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(91/3200),0,(1/4)] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00187_transform
theorem leaf00187_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00187=true := by decide +kernel
#print axioms leaf00187_sign
theorem leaf00187_log : RationalLog.accepts (2308574759/4294967296) (-666593539/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00187_log
def leaf00187 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (12916823559/62500000000) (2308574759/4294967296) (-666593539/2147483648) 1 8 ![52,0,4] ![(91/3200),0,(1/4)] ![(3/3200),1,(1/4)] affine00187
theorem leaf00187_checked : FastNestedCellData.accepts 1 0 4 leaf00187=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (12916823559/62500000000) (2308574759/4294967296) (-666593539/2147483648) 1 8 ![52,0,4] ![(91/3200),0,(1/4)] ![(3/3200),1,(1/4)] 14892083652383448052304707584000000000000 9658902186468867009044810230610352144384 46736055803261296840735195136000000000000 raw00187 affine00187
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00187_raw leaf00187_rectangular
    leaf00187_transform leaf00187_sign leaf00187_log
#print axioms leaf00187_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
