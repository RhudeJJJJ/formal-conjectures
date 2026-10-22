/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00208 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 154028072206461774162672222208000000000000 142540118932846366108931971926813021569024 4267730317798572568854671654912000000000000))
theorem leaf00208_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 154028072206461774162672222208000000000000 142540118932846366108931971926813021569024 4267730317798572568854671654912000000000000 raw00208=true := by decide +kernel
#print axioms leaf00208_raw
theorem leaf00208_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00208=true := by decide +kernel
#print axioms leaf00208_rectangular
def affine00208 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00208 (IntegerComputedClassCell.leftNumerator ![(139/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(139/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(139/32000),0,(1/4)] ![(3/32000),1,(1/4)]))
theorem leaf00208_transform : affine00208=(NestedInteger.clearedAll 3 raw00208 (IntegerComputedClassCell.leftNumerator ![(139/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(139/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(139/32000),0,(1/4)] ![(3/32000),1,(1/4)])) := by decide +kernel
#print axioms leaf00208_transform
theorem leaf00208_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00208=true := by decide +kernel
#print axioms leaf00208_sign
theorem leaf00208_log : RationalLog.accepts (3846173269/4294967296) (-237007591/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00208_log
def leaf00208 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (16699757051/500000000000) (3846173269/4294967296) (-237007591/4294967296) 1 8 ![60,0,4] ![(139/32000),0,(1/4)] ![(3/32000),1,(1/4)] affine00208
theorem leaf00208_checked : FastNestedCellData.accepts 1 2 4 leaf00208=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (16699757051/500000000000) (3846173269/4294967296) (-237007591/4294967296) 1 8 ![60,0,4] ![(139/32000),0,(1/4)] ![(3/32000),1,(1/4)] 154028072206461774162672222208000000000000 142540118932846366108931971926813021569024 4267730317798572568854671654912000000000000 raw00208 affine00208
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00208_raw leaf00208_rectangular
    leaf00208_transform leaf00208_sign leaf00208_log
#print axioms leaf00208_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
