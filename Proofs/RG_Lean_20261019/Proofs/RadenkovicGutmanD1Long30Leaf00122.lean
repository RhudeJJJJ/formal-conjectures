/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00122 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 16702859714102000109439942656000000000000 15094568009510486932113643130156463685632 347302844319171995885815988224000000000000))
theorem leaf00122_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 16702859714102000109439942656000000000000 15094568009510486932113643130156463685632 347302844319171995885815988224000000000000 raw00122=true := by decide +kernel
#print axioms leaf00122_raw
theorem leaf00122_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00122=true := by decide +kernel
#print axioms leaf00122_rectangular
def affine00122 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00122 (IntegerComputedClassCell.leftNumerator ![(11/4000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(11/4000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(11/4000),0,(1/8)] ![(3/32000),1,(1/8)]))
theorem leaf00122_transform : affine00122=(NestedInteger.clearedAll 3 raw00122 (IntegerComputedClassCell.leftNumerator ![(11/4000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(11/4000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(11/4000),0,(1/8)] ![(3/32000),1,(1/8)])) := by decide +kernel
#print axioms leaf00122_transform
theorem leaf00122_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00122=true := by decide +kernel
#print axioms leaf00122_sign
theorem leaf00122_log : RationalLog.accepts (929935821/1073741824) (-154392587/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00122_log
def leaf00122 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (43462264293/1000000000000) (929935821/1073741824) (-154392587/2147483648) 1 8 ![60,0,4] ![(11/4000),0,(1/8)] ![(3/32000),1,(1/8)] affine00122
theorem leaf00122_checked : FastNestedCellData.accepts 1 2 4 leaf00122=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (43462264293/1000000000000) (929935821/1073741824) (-154392587/2147483648) 1 8 ![60,0,4] ![(11/4000),0,(1/8)] ![(3/32000),1,(1/8)] 16702859714102000109439942656000000000000 15094568009510486932113643130156463685632 347302844319171995885815988224000000000000 raw00122 affine00122
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00122_raw leaf00122_rectangular
    leaf00122_transform leaf00122_sign leaf00122_log
#print axioms leaf00122_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
