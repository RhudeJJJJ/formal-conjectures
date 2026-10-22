/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00097 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 15175826693171454789094998016000000000000 13938113982179181255644764391532870500352 385051393511628487837045751808000000000000))
theorem leaf00097_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 15175826693171454789094998016000000000000 13938113982179181255644764391532870500352 385051393511628487837045751808000000000000 raw00097=true := by decide +kernel
#print axioms leaf00097_raw
theorem leaf00097_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00097=true := by decide +kernel
#print axioms leaf00097_rectangular
def affine00097 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00097 (IntegerComputedClassCell.leftNumerator ![(73/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(73/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(73/32000),0,(1/8)] ![(3/32000),1,(1/8)]))
theorem leaf00097_transform : affine00097=(NestedInteger.clearedAll 3 raw00097 (IntegerComputedClassCell.leftNumerator ![(73/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(73/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(73/32000),0,(1/8)] ![(3/32000),1,(1/8)])) := by decide +kernel
#print axioms leaf00097_transform
theorem leaf00097_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00097=true := by decide +kernel
#print axioms leaf00097_sign
theorem leaf00097_log : RationalLog.accepts (3806876073/4294967296) (-259061761/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00097_log
def leaf00097 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (18099030697/500000000000) (3806876073/4294967296) (-259061761/4294967296) 1 8 ![60,0,4] ![(73/32000),0,(1/8)] ![(3/32000),1,(1/8)] affine00097
theorem leaf00097_checked : FastNestedCellData.accepts 1 2 4 leaf00097=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (18099030697/500000000000) (3806876073/4294967296) (-259061761/4294967296) 1 8 ![60,0,4] ![(73/32000),0,(1/8)] ![(3/32000),1,(1/8)] 15175826693171454789094998016000000000000 13938113982179181255644764391532870500352 385051393511628487837045751808000000000000 raw00097 affine00097
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00097_raw leaf00097_rectangular
    leaf00097_transform leaf00097_sign leaf00097_log
#print axioms leaf00097_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
