/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00093 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1226191934021211662992801792000000000000 1177356217762318952087172534739377586176 69187746244039370485643870208000000000000))
theorem leaf00093_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1226191934021211662992801792000000000000 1177356217762318952087172534739377586176 69187746244039370485643870208000000000000 raw00093=true := by decide +kernel
#print axioms leaf00093_raw
theorem leaf00093_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00093=true := by decide +kernel
#print axioms leaf00093_rectangular
def affine00093 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00093 (IntegerComputedClassCell.leftNumerator ![(7/3200),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/3200),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/3200),0,(1/4)] ![(3/32000),1,(1/4)]))
theorem leaf00093_transform : affine00093=(NestedInteger.clearedAll 3 raw00093 (IntegerComputedClassCell.leftNumerator ![(7/3200),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/3200),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/3200),0,(1/4)] ![(3/32000),1,(1/4)])) := by decide +kernel
#print axioms leaf00093_transform
theorem leaf00093_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00093=true := by decide +kernel
#print axioms leaf00093_sign
theorem leaf00093_log : RationalLog.accepts (4054909329/4294967296) (-123513877/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00093_log
def leaf00093 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (1063551967/62500000000) (4054909329/4294967296) (-123513877/4294967296) 1 8 ![60,0,4] ![(7/3200),0,(1/4)] ![(3/32000),1,(1/4)] affine00093
theorem leaf00093_checked : FastNestedCellData.accepts 1 2 4 leaf00093=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (1063551967/62500000000) (4054909329/4294967296) (-123513877/4294967296) 1 8 ![60,0,4] ![(7/3200),0,(1/4)] ![(3/32000),1,(1/4)] 1226191934021211662992801792000000000000 1177356217762318952087172534739377586176 69187746244039370485643870208000000000000 raw00093 affine00093
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00093_raw leaf00093_rectangular
    leaf00093_transform leaf00093_sign leaf00093_log
#print axioms leaf00093_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
