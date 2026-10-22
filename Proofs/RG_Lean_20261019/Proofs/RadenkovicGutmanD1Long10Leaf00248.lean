/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00248 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 7536849077480750845090647244800000000000 5454830250984858161786544388430610038784 33377296192018484871344370483200000000000))
theorem leaf00248_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 7536849077480750845090647244800000000000 5454830250984858161786544388430610038784 33377296192018484871344370483200000000000 raw00248=true := by decide +kernel
#print axioms leaf00248_raw
theorem leaf00248_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00248=true := by decide +kernel
#print axioms leaf00248_rectangular
def affine00248 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00248 (IntegerComputedClassCell.leftNumerator ![(151/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(151/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(151/3200),0,(1/2)] ![(3/3200),1,(1/2)]))
theorem leaf00248_transform : affine00248=(NestedInteger.clearedAll 3 raw00248 (IntegerComputedClassCell.leftNumerator ![(151/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(151/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(151/3200),0,(1/2)] ![(3/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00248_transform
theorem leaf00248_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00248=true := by decide +kernel
#print axioms leaf00248_sign
theorem leaf00248_log : RationalLog.accepts (1335922507/2147483648) (-254839043/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00248_log
def leaf00248 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (16342936287/100000000000) (1335922507/2147483648) (-254839043/1073741824) 1 8 ![52,0,4] ![(151/3200),0,(1/2)] ![(3/3200),1,(1/2)] affine00248
theorem leaf00248_checked : FastNestedCellData.accepts 1 0 4 leaf00248=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (16342936287/100000000000) (1335922507/2147483648) (-254839043/1073741824) 1 8 ![52,0,4] ![(151/3200),0,(1/2)] ![(3/3200),1,(1/2)] 7536849077480750845090647244800000000000 5454830250984858161786544388430610038784 33377296192018484871344370483200000000000 raw00248 affine00248
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00248_raw leaf00248_rectangular
    leaf00248_transform leaf00248_sign leaf00248_log
#print axioms leaf00248_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
