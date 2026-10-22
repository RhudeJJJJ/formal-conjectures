/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00794 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 41521143673888342515944259584000000000000 31011263880161902250888443201201020862464 215273170780702658113069645824000000000000))
theorem leaf00794_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 41521143673888342515944259584000000000000 31011263880161902250888443201201020862464 215273170780702658113069645824000000000000 raw00794=true := by decide +kernel
#print axioms leaf00794_raw
theorem leaf00794_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00794=true := by decide +kernel
#print axioms leaf00794_rectangular
def affine00794 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00794 (IntegerComputedClassCell.leftNumerator ![(13/320),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(13/320),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(13/320),0,(1/2)] ![(3/3200),1,(1/2)]))
theorem leaf00794_transform : affine00794=(NestedInteger.clearedAll 3 raw00794 (IntegerComputedClassCell.leftNumerator ![(13/320),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(13/320),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(13/320),0,(1/2)] ![(3/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00794_transform
theorem leaf00794_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00794=true := by decide +kernel
#print axioms leaf00794_sign
theorem leaf00794_log : RationalLog.accepts (350487857/536870912) (-915754961/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00794_log
def leaf00794 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (144055405361/1000000000000) (350487857/536870912) (-915754961/4294967296) 1 8 ![60,0,4] ![(13/320),0,(1/2)] ![(3/3200),1,(1/2)] affine00794
theorem leaf00794_checked : FastNestedCellData.accepts 1 2 4 leaf00794=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (144055405361/1000000000000) (350487857/536870912) (-915754961/4294967296) 1 8 ![60,0,4] ![(13/320),0,(1/2)] ![(3/3200),1,(1/2)] 41521143673888342515944259584000000000000 31011263880161902250888443201201020862464 215273170780702658113069645824000000000000 raw00794 affine00794
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00794_raw leaf00794_rectangular
    leaf00794_transform leaf00794_sign leaf00794_log
#print axioms leaf00794_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
