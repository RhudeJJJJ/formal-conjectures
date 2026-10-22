/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00187 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1148908552437579698486779052032000000000000 996027288738138501828846038370250534158336 15992100021190747063501316947968000000000000))
theorem leaf00187_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1148908552437579698486779052032000000000000 996027288738138501828846038370250534158336 15992100021190747063501316947968000000000000 raw00187=true := by decide +kernel
#print axioms leaf00187_raw
theorem leaf00187_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00187=true := by decide +kernel
#print axioms leaf00187_rectangular
def affine00187 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00187 (IntegerComputedClassCell.leftNumerator ![(127/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(127/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(127/32000),0,(1/8)] ![(3/32000),1,(1/8)]))
theorem leaf00187_transform : affine00187=(NestedInteger.clearedAll 3 raw00187 (IntegerComputedClassCell.leftNumerator ![(127/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(127/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(127/32000),0,(1/8)] ![(3/32000),1,(1/8)])) := by decide +kernel
#print axioms leaf00187_transform
theorem leaf00187_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00187=true := by decide +kernel
#print axioms leaf00187_sign
theorem leaf00187_log : RationalLog.accepts (3505142079/4294967296) (-13637387/134217728) 1 8=true := by decide +kernel
#print axioms leaf00187_log
def leaf00187 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (62282457427/1000000000000) (3505142079/4294967296) (-13637387/134217728) 1 8 ![60,0,4] ![(127/32000),0,(1/8)] ![(3/32000),1,(1/8)] affine00187
theorem leaf00187_checked : FastNestedCellData.accepts 1 2 4 leaf00187=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (62282457427/1000000000000) (3505142079/4294967296) (-13637387/134217728) 1 8 ![60,0,4] ![(127/32000),0,(1/8)] ![(3/32000),1,(1/8)] 1148908552437579698486779052032000000000000 996027288738138501828846038370250534158336 15992100021190747063501316947968000000000000 raw00187 affine00187
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00187_raw leaf00187_rectangular
    leaf00187_transform leaf00187_sign leaf00187_log
#print axioms leaf00187_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
