/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00084 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 139396203305450051442434899968000000000000 136858618757818868211759392035821984940032 18110937418968889112433088528384000000000000))
theorem leaf00084_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 139396203305450051442434899968000000000000 136858618757818868211759392035821984940032 18110937418968889112433088528384000000000000 raw00084=true := by decide +kernel
#print axioms leaf00084_raw
theorem leaf00084_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00084=true := by decide +kernel
#print axioms leaf00084_rectangular
def affine00084 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00084 (IntegerComputedClassCell.leftNumerator ![(1/500),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/500),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/500),0,(1/2)] ![(3/32000),1,(1/2)]))
theorem leaf00084_transform : affine00084=(NestedInteger.clearedAll 3 raw00084 (IntegerComputedClassCell.leftNumerator ![(1/500),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/500),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/500),0,(1/2)] ![(3/32000),1,(1/2)])) := by decide +kernel
#print axioms leaf00084_transform
theorem leaf00084_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00084=true := by decide +kernel
#print axioms leaf00084_sign
theorem leaf00084_log : RationalLog.accepts (4185155323/4294967296) (-55620129/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00084_log
def leaf00084 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (7556683323/1000000000000) (4185155323/4294967296) (-55620129/4294967296) 1 8 ![60,0,4] ![(1/500),0,(1/2)] ![(3/32000),1,(1/2)] affine00084
theorem leaf00084_checked : FastNestedCellData.accepts 1 2 4 leaf00084=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (7556683323/1000000000000) (4185155323/4294967296) (-55620129/4294967296) 1 8 ![60,0,4] ![(1/500),0,(1/2)] ![(3/32000),1,(1/2)] 139396203305450051442434899968000000000000 136858618757818868211759392035821984940032 18110937418968889112433088528384000000000000 raw00084 affine00084
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00084_raw leaf00084_rectangular
    leaf00084_transform leaf00084_sign leaf00084_log
#print axioms leaf00084_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
