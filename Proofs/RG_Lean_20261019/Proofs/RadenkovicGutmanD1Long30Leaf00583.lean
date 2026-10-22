/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00583 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 101668028554585593783474150440960000000000 75419023089072692600279173082092878692352 547363979411230871740238266368000000000000))
theorem leaf00583_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 101668028554585593783474150440960000000000 75419023089072692600279173082092878692352 547363979411230871740238266368000000000000 raw00583=true := by decide +kernel
#print axioms leaf00583_raw
theorem leaf00583_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00583=true := by decide +kernel
#print axioms leaf00583_rectangular
def affine00583 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00583 (IntegerComputedClassCell.leftNumerator ![(59/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(59/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(59/3200),0,(1/4)] ![(1/3200),1,(1/4)]))
theorem leaf00583_transform : affine00583=(NestedInteger.clearedAll 3 raw00583 (IntegerComputedClassCell.leftNumerator ![(59/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(59/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(59/3200),0,(1/4)] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00583_transform
theorem leaf00583_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00583=true := by decide +kernel
#print axioms leaf00583_sign
theorem leaf00583_log : RationalLog.accepts (2800243675/4294967296) (-229639831/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00583_log
def leaf00583 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (137785871789/1000000000000) (2800243675/4294967296) (-229639831/1073741824) 1 8 ![60,0,4] ![(59/3200),0,(1/4)] ![(1/3200),1,(1/4)] affine00583
theorem leaf00583_checked : FastNestedCellData.accepts 1 2 4 leaf00583=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (137785871789/1000000000000) (2800243675/4294967296) (-229639831/1073741824) 1 8 ![60,0,4] ![(59/3200),0,(1/4)] ![(1/3200),1,(1/4)] 101668028554585593783474150440960000000000 75419023089072692600279173082092878692352 547363979411230871740238266368000000000000 raw00583 affine00583
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00583_raw leaf00583_rectangular
    leaf00583_transform leaf00583_sign leaf00583_log
#print axioms leaf00583_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
