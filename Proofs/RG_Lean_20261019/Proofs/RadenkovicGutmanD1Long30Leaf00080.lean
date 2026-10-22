/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00080 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 882461346495588004998208815104000000000000 45922246656714277942283600739113631744 239986695941477040383852544000000000000))
theorem leaf00080_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 882461346495588004998208815104000000000000 45922246656714277942283600739113631744 239986695941477040383852544000000000000 raw00080=true := by decide +kernel
#print axioms leaf00080_raw
theorem leaf00080_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00080=true := by decide +kernel
#print axioms leaf00080_rectangular
def affine00080 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00080 (IntegerComputedClassCell.leftNumerator ![(1/500),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/500),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/500),0,0] ![(3/32000),1,(1/16)]))
theorem leaf00080_transform : affine00080=(NestedInteger.clearedAll 3 raw00080 (IntegerComputedClassCell.leftNumerator ![(1/500),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/500),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/500),0,0] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00080_transform
theorem leaf00080_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00080=true := by decide +kernel
#print axioms leaf00080_sign
theorem leaf00080_log : RationalLog.accepts (93803/2147483648) (-21557752383/4294967296) 15 8=true := by decide +kernel
#print axioms leaf00080_log
def leaf00080 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (191353301801/1000000000000) (93803/2147483648) (-21557752383/4294967296) 15 8 ![60,0,4] ![(1/500),0,0] ![(3/32000),1,(1/16)] affine00080
theorem leaf00080_checked : FastNestedCellData.accepts 1 2 4 leaf00080=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (191353301801/1000000000000) (93803/2147483648) (-21557752383/4294967296) 15 8 ![60,0,4] ![(1/500),0,0] ![(3/32000),1,(1/16)] 882461346495588004998208815104000000000000 45922246656714277942283600739113631744 239986695941477040383852544000000000000 raw00080 affine00080
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00080_raw leaf00080_rectangular
    leaf00080_transform leaf00080_sign leaf00080_log
#print axioms leaf00080_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
