/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00283 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 1431987498026118804219736201625600000000000 739743868169649767207959121282730251255808 1905863820044687602278073368576000000000000))
theorem leaf00283_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 1431987498026118804219736201625600000000000 739743868169649767207959121282730251255808 1905863820044687602278073368576000000000000 raw00283=true := by decide +kernel
#print axioms leaf00283_raw
theorem leaf00283_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00283=true := by decide +kernel
#print axioms leaf00283_rectangular
def affine00283 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00283 (IntegerComputedClassCell.leftNumerator ![(21/320),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(21/320),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(21/320),0,(1/4)] ![(1/640),1,(1/4)]))
theorem leaf00283_transform : affine00283=(NestedInteger.clearedAll 3 raw00283 (IntegerComputedClassCell.leftNumerator ![(21/320),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(21/320),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(21/320),0,(1/4)] ![(1/640),1,(1/4)])) := by decide +kernel
#print axioms leaf00283_transform
theorem leaf00283_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00283=true := by decide +kernel
#print axioms leaf00283_sign
theorem leaf00283_log : RationalLog.accepts (1598337285/4294967296) (-530686203/1073741824) 2 8=true := by decide +kernel
#print axioms leaf00283_log
def leaf00283 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (388140989083/1000000000000) (1598337285/4294967296) (-530686203/1073741824) 2 8 ![52,0,4] ![(21/320),0,(1/4)] ![(1/640),1,(1/4)] affine00283
theorem leaf00283_checked : FastNestedCellData.accepts 1 0 4 leaf00283=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (388140989083/1000000000000) (1598337285/4294967296) (-530686203/1073741824) 2 8 ![52,0,4] ![(21/320),0,(1/4)] ![(1/640),1,(1/4)] 1431987498026118804219736201625600000000000 739743868169649767207959121282730251255808 1905863820044687602278073368576000000000000 raw00283 affine00283
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00283_raw leaf00283_rectangular
    leaf00283_transform leaf00283_sign leaf00283_log
#print axioms leaf00283_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
