/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00157 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 247230802882000082340331651072000000000000 218462475027592479736990984598884959911936 4075059943548568905900728778752000000000000))
theorem leaf00157_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 247230802882000082340331651072000000000000 218462475027592479736990984598884959911936 4075059943548568905900728778752000000000000 raw00157=true := by decide +kernel
#print axioms leaf00157_raw
theorem leaf00157_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00157=true := by decide +kernel
#print axioms leaf00157_rectangular
def affine00157 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00157 (IntegerComputedClassCell.leftNumerator ![(109/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(109/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(109/32000),0,(1/8)] ![(3/32000),1,(1/8)]))
theorem leaf00157_transform : affine00157=(NestedInteger.clearedAll 3 raw00157 (IntegerComputedClassCell.leftNumerator ![(109/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(109/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(109/32000),0,(1/8)] ![(3/32000),1,(1/8)])) := by decide +kernel
#print axioms leaf00157_transform
theorem leaf00157_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00157=true := by decide +kernel
#print axioms leaf00157_sign
theorem leaf00157_log : RationalLog.accepts (3602088661/4294967296) (-188903503/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00157_log
def leaf00157 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (26804817359/500000000000) (3602088661/4294967296) (-188903503/2147483648) 1 8 ![60,0,4] ![(109/32000),0,(1/8)] ![(3/32000),1,(1/8)] affine00157
theorem leaf00157_checked : FastNestedCellData.accepts 1 2 4 leaf00157=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (26804817359/500000000000) (3602088661/4294967296) (-188903503/2147483648) 1 8 ![60,0,4] ![(109/32000),0,(1/8)] ![(3/32000),1,(1/8)] 247230802882000082340331651072000000000000 218462475027592479736990984598884959911936 4075059943548568905900728778752000000000000 raw00157 affine00157
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00157_raw leaf00157_rectangular
    leaf00157_transform leaf00157_sign leaf00157_log
#print axioms leaf00157_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
