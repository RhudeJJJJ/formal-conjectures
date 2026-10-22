/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00927 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 686012137664706749343104761856000000000000 278984301512857643278944721428278560161792 468864882998763091697841733632000000000000))
theorem leaf00927_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 686012137664706749343104761856000000000000 278984301512857643278944721428278560161792 468864882998763091697841733632000000000000 raw00927=true := by decide +kernel
#print axioms leaf00927_raw
theorem leaf00927_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00927=true := by decide +kernel
#print axioms leaf00927_rectangular
def affine00927 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00927 (IntegerComputedClassCell.leftNumerator ![(13/160),0,(1/8)] ![(1/320),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(13/160),0,(1/8)] ![(1/320),1,(1/8)]) (IntegerComputedClassCell.denominator ![(13/160),0,(1/8)] ![(1/320),1,(1/8)]))
theorem leaf00927_transform : affine00927=(NestedInteger.clearedAll 3 raw00927 (IntegerComputedClassCell.leftNumerator ![(13/160),0,(1/8)] ![(1/320),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(13/160),0,(1/8)] ![(1/320),1,(1/8)]) (IntegerComputedClassCell.denominator ![(13/160),0,(1/8)] ![(1/320),1,(1/8)])) := by decide +kernel
#print axioms leaf00927_transform
theorem leaf00927_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00927=true := by decide +kernel
#print axioms leaf00927_sign
theorem leaf00927_log : RationalLog.accepts (547534531/2147483648) (-2934808153/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00927_log
def leaf00927 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (297510340003/500000000000) (547534531/2147483648) (-2934808153/4294967296) 2 8 ![60,0,4] ![(13/160),0,(1/8)] ![(1/320),1,(1/8)] affine00927
theorem leaf00927_checked : FastNestedCellData.accepts 1 2 4 leaf00927=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (297510340003/500000000000) (547534531/2147483648) (-2934808153/4294967296) 2 8 ![60,0,4] ![(13/160),0,(1/8)] ![(1/320),1,(1/8)] 686012137664706749343104761856000000000000 278984301512857643278944721428278560161792 468864882998763091697841733632000000000000 raw00927 affine00927
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00927_raw leaf00927_rectangular
    leaf00927_transform leaf00927_sign leaf00927_log
#print axioms leaf00927_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
