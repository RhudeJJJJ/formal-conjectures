/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00777 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 131763338901488397611972952064000000000000 54315040837941359328165976465513180561408 118813357204919623655115194368000000000000))
theorem leaf00777_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 131763338901488397611972952064000000000000 54315040837941359328165976465513180561408 118813357204919623655115194368000000000000 raw00777=true := by decide +kernel
#print axioms leaf00777_raw
theorem leaf00777_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00777=true := by decide +kernel
#print axioms leaf00777_rectangular
def affine00777 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00777 (IntegerComputedClassCell.leftNumerator ![(121/3200),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(121/3200),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(121/3200),0,(1/8)] ![(3/3200),1,(1/8)]))
theorem leaf00777_transform : affine00777=(NestedInteger.clearedAll 3 raw00777 (IntegerComputedClassCell.leftNumerator ![(121/3200),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(121/3200),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(121/3200),0,(1/8)] ![(3/3200),1,(1/8)])) := by decide +kernel
#print axioms leaf00777_transform
theorem leaf00777_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00777=true := by decide +kernel
#print axioms leaf00777_sign
theorem leaf00777_log : RationalLog.accepts (151877119/536870912) (-677899355/1073741824) 2 8=true := by decide +kernel
#print axioms leaf00777_log
def leaf00777 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (457145914531/1000000000000) (151877119/536870912) (-677899355/1073741824) 2 8 ![60,0,4] ![(121/3200),0,(1/8)] ![(3/3200),1,(1/8)] affine00777
theorem leaf00777_checked : FastNestedCellData.accepts 1 2 4 leaf00777=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (457145914531/1000000000000) (151877119/536870912) (-677899355/1073741824) 2 8 ![60,0,4] ![(121/3200),0,(1/8)] ![(3/3200),1,(1/8)] 131763338901488397611972952064000000000000 54315040837941359328165976465513180561408 118813357204919623655115194368000000000000 raw00777 affine00777
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00777_raw leaf00777_rectangular
    leaf00777_transform leaf00777_sign leaf00777_log
#print axioms leaf00777_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
