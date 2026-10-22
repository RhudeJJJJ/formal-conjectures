/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00080 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 63924027620343672536664375296000000000000 59341979933408395616137009501946461028352 1902721015362891417499297906688000000000000))
theorem leaf00080_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 63924027620343672536664375296000000000000 59341979933408395616137009501946461028352 1902721015362891417499297906688000000000000 raw00080=true := by decide +kernel
#print axioms leaf00080_raw
theorem leaf00080_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00080=true := by decide +kernel
#print axioms leaf00080_rectangular
def affine00080 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00080 (IntegerComputedClassCell.leftNumerator ![(27/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(27/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(27/3200),0,(1/2)] ![(1/3200),1,(1/2)]))
theorem leaf00080_transform : affine00080=(NestedInteger.clearedAll 3 raw00080 (IntegerComputedClassCell.leftNumerator ![(27/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(27/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(27/3200),0,(1/2)] ![(1/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00080_transform
theorem leaf00080_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00080=true := by decide +kernel
#print axioms leaf00080_sign
theorem leaf00080_log : RationalLog.accepts (3866517063/4294967296) (-28209839/536870912) 1 8=true := by decide +kernel
#print axioms leaf00080_log
def leaf00080 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (31187956329/1000000000000) (3866517063/4294967296) (-28209839/536870912) 1 8 ![52,0,4] ![(27/3200),0,(1/2)] ![(1/3200),1,(1/2)] affine00080
theorem leaf00080_checked : FastNestedCellData.accepts 1 0 4 leaf00080=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (31187956329/1000000000000) (3866517063/4294967296) (-28209839/536870912) 1 8 ![52,0,4] ![(27/3200),0,(1/2)] ![(1/3200),1,(1/2)] 63924027620343672536664375296000000000000 59341979933408395616137009501946461028352 1902721015362891417499297906688000000000000 raw00080 affine00080
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00080_raw leaf00080_rectangular
    leaf00080_transform leaf00080_sign leaf00080_log
#print axioms leaf00080_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
