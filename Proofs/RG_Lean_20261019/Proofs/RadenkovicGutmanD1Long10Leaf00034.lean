/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00034 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 1609453188916968283340957286400000000000 1500042387940907393877167412595535118336 53727288832881363880784166912000000000000))
theorem leaf00034_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 1609453188916968283340957286400000000000 1500042387940907393877167412595535118336 53727288832881363880784166912000000000000 raw00034=true := by decide +kernel
#print axioms leaf00034_raw
theorem leaf00034_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00034=true := by decide +kernel
#print axioms leaf00034_rectangular
def affine00034 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00034 (IntegerComputedClassCell.leftNumerator ![(7/2000),0,(1/4)] ![(3/8000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/2000),0,(1/4)] ![(3/8000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/2000),0,(1/4)] ![(3/8000),1,(1/4)]))
theorem leaf00034_transform : affine00034=(NestedInteger.clearedAll 3 raw00034 (IntegerComputedClassCell.leftNumerator ![(7/2000),0,(1/4)] ![(3/8000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/2000),0,(1/4)] ![(3/8000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/2000),0,(1/4)] ![(3/8000),1,(1/4)])) := by decide +kernel
#print axioms leaf00034_transform
theorem leaf00034_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00034=true := by decide +kernel
#print axioms leaf00034_sign
theorem leaf00034_log : RationalLog.accepts (486783585/536870912) (-210320371/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00034_log
def leaf00034 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (27919562303/1000000000000) (486783585/536870912) (-210320371/4294967296) 1 8 ![52,0,4] ![(7/2000),0,(1/4)] ![(3/8000),1,(1/4)] affine00034
theorem leaf00034_checked : FastNestedCellData.accepts 1 0 4 leaf00034=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (27919562303/1000000000000) (486783585/536870912) (-210320371/4294967296) 1 8 ![52,0,4] ![(7/2000),0,(1/4)] ![(3/8000),1,(1/4)] 1609453188916968283340957286400000000000 1500042387940907393877167412595535118336 53727288832881363880784166912000000000000 raw00034 affine00034
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00034_raw leaf00034_rectangular
    leaf00034_transform leaf00034_sign leaf00034_log
#print axioms leaf00034_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
