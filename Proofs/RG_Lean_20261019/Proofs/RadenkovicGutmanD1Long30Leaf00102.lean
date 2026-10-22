/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00102 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 347276994222250533802026729472000000000 317921480375204679022947979889083416576 8443715364950195829592817664000000000000))
theorem leaf00102_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 347276994222250533802026729472000000000 317921480375204679022947979889083416576 8443715364950195829592817664000000000000 raw00102=true := by decide +kernel
#print axioms leaf00102_raw
theorem leaf00102_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00102=true := by decide +kernel
#print axioms leaf00102_rectangular
def affine00102 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00102 (IntegerComputedClassCell.leftNumerator ![(19/8000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(19/8000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(19/8000),0,(1/8)] ![(3/32000),1,(1/8)]))
theorem leaf00102_transform : affine00102=(NestedInteger.clearedAll 3 raw00102 (IntegerComputedClassCell.leftNumerator ![(19/8000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(19/8000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(19/8000),0,(1/8)] ![(3/32000),1,(1/8)])) := by decide +kernel
#print axioms leaf00102_transform
theorem leaf00102_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00102=true := by decide +kernel
#print axioms leaf00102_sign
theorem leaf00102_log : RationalLog.accepts (947309875/1073741824) (-33629223/536870912) 1 8=true := by decide +kernel
#print axioms leaf00102_log
def leaf00102 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (37651847159/1000000000000) (947309875/1073741824) (-33629223/536870912) 1 8 ![60,0,4] ![(19/8000),0,(1/8)] ![(3/32000),1,(1/8)] affine00102
theorem leaf00102_checked : FastNestedCellData.accepts 1 2 4 leaf00102=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (37651847159/1000000000000) (947309875/1073741824) (-33629223/536870912) 1 8 ![60,0,4] ![(19/8000),0,(1/8)] ![(3/32000),1,(1/8)] 347276994222250533802026729472000000000 317921480375204679022947979889083416576 8443715364950195829592817664000000000000 raw00102 affine00102
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00102_raw leaf00102_rectangular
    leaf00102_transform leaf00102_sign leaf00102_log
#print axioms leaf00102_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
